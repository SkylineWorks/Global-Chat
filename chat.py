#!/usr/bin/env python3
"""
chat.py - Discord-inspired CustomTkinter chat client

Install:
    py -m pip install customtkinter requests pillow
    py -m pip install numpy sounddevice opencv-python

Run:
    python chat.py

Call notes:
    With sounddevice, CHAT_AUDIO_DEVICE can be a sounddevice input index/name.
    With Windows DirectShow fallback, use CHAT_DSHOW_DEVICE=audio=Microphone Name.
    To hear people, install one playback backend:
        py -m pip install sounddevice
    or:
        py -m pip install pyaudio
    For webcam video:
        py -m pip install opencv-python
"""

import base64
import io
import json
import html
import math
import mimetypes
import os
import platform
import queue
import re
import struct
import subprocess
import sys
import threading
import time
import webbrowser
from fractions import Fraction
from urllib.parse import quote, urljoin

import requests
import customtkinter as ctk
import tkinter as tk
from tkinter import colorchooser, filedialog, messagebox, simpledialog

try:
    from PIL import Image, ImageDraw, ImageOps, ImageTk
except ImportError:
    Image = ImageDraw = ImageOps = ImageTk = None


BASE_URL = os.environ.get("CHAT_BASE_URL", "https://dwarfthe3.pythonanywhere.com")
IS_WINDOWS = platform.system().lower() == "windows"

g_username = ""
g_password = ""
g_current_dm = ""
g_dm_lock = threading.Lock()
g_last_id = -1
g_last_dm_id = -1
g_profiles = {}
g_chat_messages = []
g_contacts = {}
g_online_users = set()

if IS_WINDOWS:
    APP_DATA_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "Global Chat")
else:
    APP_DATA_DIR = os.path.join(os.path.expanduser("~"), ".global_chat")
CONTACTS_FILE = os.path.join(APP_DATA_DIR, "contacts.json")

try:
    import asyncio
    from aiortc import MediaStreamTrack, RTCConfiguration, RTCIceServer, RTCPeerConnection, RTCSessionDescription
    from aiortc.sdp import candidate_from_sdp, candidate_to_sdp

    WEBRTC = True
except ImportError:
    WEBRTC = False


g_call = {
    "active": False,
    "peer": "",
    "session_id": "",
    "pc": None,
    "loop": None,
    "pending": False,
    "pending_caller": "",
    "pending_sdp": "",
    "pending_sid": "",
    "pending_ice": [],
    "audio_players": [],
    "relay": None,
    "video": None,
    "mic_error": "",
}
g_call_lock = threading.Lock()


class RemoteAudioPlayer:
    def __init__(self):
        self._backend = None
        self._stream = None
        self._pa = None
        self._resampler = None
        self._last_error = ""
        try:
            import av
            import sounddevice as sd

            self._av = av
            self._sd = sd
            self._stream = sd.OutputStream(samplerate=48000, channels=2, dtype="int16")
            self._stream.start()
            self._resampler = av.AudioResampler(format="s16", layout="stereo", rate=48000)
            self._backend = "sounddevice"
            app_signals.call_status.emit("Playing audio with sounddevice")
            return
        except Exception as exc:
            self._last_error = f"sounddevice failed: {exc}"

        try:
            import av
            import pyaudio

            self._av = av
            self._pa = pyaudio.PyAudio()
            self._stream = self._pa.open(
                format=pyaudio.paInt16,
                channels=2,
                rate=48000,
                output=True,
            )
            self._resampler = av.AudioResampler(format="s16", layout="stereo", rate=48000)
            self._backend = "pyaudio"
            app_signals.call_status.emit("Playing audio with pyaudio")
        except Exception as exc:
            self._last_error = f"{self._last_error}; pyaudio failed: {exc}" if self._last_error else f"pyaudio failed: {exc}"
            self._backend = None

    @property
    def available(self):
        return self._backend is not None

    def write_frame(self, frame):
        if not self.available:
            return
        converted_frames = self._resampler.resample(frame)
        if converted_frames is None:
            return
        if not isinstance(converted_frames, (list, tuple)):
            converted_frames = [converted_frames]
        for converted in converted_frames:
            if converted.planes:
                if self._backend == "sounddevice":
                    samples = converted.to_ndarray()
                    if samples.ndim == 1:
                        samples = samples.reshape(-1, 2)
                    elif samples.shape[0] == 1:
                        samples = samples.reshape(-1, 2)
                    else:
                        samples = samples.T
                    self._stream.write(samples)
                else:
                    self.write_pcm(bytes(converted.planes[0]))

    def write_pcm(self, pcm):
        if not self.available:
            return
        if self._backend == "sounddevice":
            import numpy as np

            samples = np.frombuffer(pcm, dtype=np.int16).reshape(-1, 2)
            self._stream.write(samples)
        else:
            self._stream.write(pcm)

    def close(self):
        try:
            if self._stream:
                self._stream.stop()
                self._stream.close()
        except Exception:
            pass
        try:
            if self._pa:
                self._pa.terminate()
        except Exception:
            pass


if WEBRTC:
    class SoundDeviceMicrophoneTrack(MediaStreamTrack):
        kind = "audio"

        def __init__(self, device=None, samplerate=48000, channels=1):
            super().__init__()
            import av
            import numpy as np
            import sounddevice as sd

            self._av = av
            self._np = np
            self._sd = sd
            self._samplerate = samplerate
            self._channels = channels
            self._pts = 0
            self._queue = queue.Queue(maxsize=60)
            self._stream = sd.InputStream(
                device=device,
                samplerate=samplerate,
                channels=channels,
                dtype="int16",
                blocksize=960,
                callback=self._callback,
            )
            self._stream.start()

        def _callback(self, indata, frames, time_info, status):
            if status:
                app_signals.call_status.emit(f"Mic status: {status}")
            try:
                self._queue.put_nowait(indata.copy())
            except queue.Full:
                try:
                    self._queue.get_nowait()
                    self._queue.put_nowait(indata.copy())
                except Exception:
                    pass

        async def recv(self):
            loop = asyncio.get_event_loop()
            samples = await loop.run_in_executor(None, self._queue.get)
            if samples.ndim == 1:
                samples = samples.reshape(1, -1)
            else:
                samples = samples.T
            frame = self._av.AudioFrame.from_ndarray(samples, format="s16", layout="mono")
            frame.sample_rate = self._samplerate
            frame.pts = self._pts
            frame.time_base = Fraction(1, self._samplerate)
            self._pts += frame.samples
            return frame

        def stop(self):
            super().stop()
            try:
                self._stream.stop()
                self._stream.close()
            except Exception:
                pass


def _sounddevice_input_summary():
    try:
        import sounddevice as sd

        default_input = sd.default.device[0]
        devices = sd.query_devices()
        if default_input is None or default_input < 0:
            return "sounddevice has no default input device"
        device = devices[default_input]
        return (
            f"default input #{default_input}: {device.get('name', 'unknown')}, "
            f"inputs={device.get('max_input_channels', '?')}, "
            f"default_sr={int(device.get('default_samplerate', 0) or 0)}"
        )
    except Exception as exc:
        return f"could not query sounddevice devices: {exc}"


def _sounddevice_env_device():
    value = os.environ.get("CHAT_AUDIO_DEVICE")
    if not value or value.startswith("audio="):
        return None
    try:
        return int(value)
    except ValueError:
        return value


class RelayAudioSession:
    def __init__(self, peer, session_id):
        import numpy as np
        import sounddevice as sd

        self.peer = peer
        self.session_id = session_id
        self.rate = int(os.environ.get("CHAT_RELAY_RATE", "16000"))
        self.channels = 1
        self._np = np
        self._sd = sd
        self._seq = 0
        self._stop = threading.Event()
        self._send_queue = queue.Queue(maxsize=30)
        self._play_queue = queue.Queue(maxsize=80)
        self._play_started = False
        self._underruns = 0
        self._relay_batch = int(os.environ.get("CHAT_RELAY_BATCH", "3"))
        self._blocksize = self.rate // 10
        self._http = requests.Session()
        self._input = sd.InputStream(
            device=_sounddevice_env_device(),
            samplerate=self.rate,
            channels=self.channels,
            dtype="int16",
            blocksize=self._blocksize,
            callback=self._input_callback,
        )
        self._output = sd.OutputStream(
            samplerate=self.rate,
            channels=self.channels,
            dtype="int16",
            blocksize=self._blocksize,
        )

    def _input_callback(self, indata, frames, time_info, status):
        if status:
            app_signals.call_status.emit(f"Relay mic: {status}")
        try:
            self._send_queue.put_nowait(indata.copy().tobytes())
        except queue.Full:
            try:
                self._send_queue.get_nowait()
                self._send_queue.put_nowait(indata.copy().tobytes())
            except Exception:
                pass

    def start(self):
        self._input.start()
        self._output.start()
        threading.Thread(target=self._send_loop, daemon=True).start()
        threading.Thread(target=self._receive_loop, daemon=True).start()
        threading.Thread(target=self._playback_loop, daemon=True).start()
        app_signals.call_status.emit("Relay audio active")

    def stop(self):
        self._stop.set()
        for stream in (self._input, self._output):
            try:
                stream.stop()
                stream.close()
            except Exception:
                pass

    def _send_loop(self):
        while not self._stop.is_set():
            try:
                pcm = self._send_queue.get(timeout=0.25)
            except queue.Empty:
                continue
            chunks = [pcm]
            for _ in range(max(1, self._relay_batch) - 1):
                try:
                    chunks.append(self._send_queue.get_nowait())
                except queue.Empty:
                    break
            pcm = b"".join(chunks)
            self._seq += 1
            try:
                self._http.post(
                    BASE_URL + "/relay_audio_send",
                    json={
                    "username": g_username,
                    "password": g_password,
                    "target": self.peer,
                    "session_id": self.session_id,
                    "audio": base64.b64encode(pcm).decode("ascii"),
                    "seq": self._seq,
                    "rate": self.rate,
                    "channels": self.channels,
                    },
                    timeout=4,
                )
            except Exception:
                pass

    def _receive_loop(self):
        frames = 0
        while not self._stop.is_set():
            try:
                response = self._http.get(
                    BASE_URL + f"/relay_audio_poll?username={quote(g_username)}&session_id={quote(self.session_id)}",
                    timeout=4,
                )
                data = response.json()
            except Exception:
                data = None
            if isinstance(data, dict):
                chunks = sorted(data.get("chunks", []), key=lambda item: item.get("seq", 0))
                for chunk in chunks:
                    try:
                        pcm = base64.b64decode(chunk.get("audio", ""))
                        samples = self._np.frombuffer(pcm, dtype=self._np.int16).reshape(-1, self.channels)
                        try:
                            self._play_queue.put_nowait(samples.copy())
                        except queue.Full:
                            self._play_queue.get_nowait()
                            self._play_queue.put_nowait(samples.copy())
                        frames += 1
                        if frames == 1 or frames % 25 == 0:
                            app_signals.call_status.emit(f"Relay audio chunks: {frames}")
                    except Exception as exc:
                        app_signals.call_status.emit(f"Relay playback error: {exc}")
            time.sleep(0.04)

    def _playback_loop(self):
        silence = self._np.zeros((self._blocksize, self.channels), dtype=self._np.int16)
        while not self._stop.is_set():
            try:
                if not self._play_started:
                    while self._play_queue.qsize() < 2 and not self._stop.is_set():
                        time.sleep(0.02)
                    self._play_started = True
                samples = self._play_queue.get(timeout=0.15)
                self._output.write(samples)
            except queue.Empty:
                self._underruns += 1
                if self._underruns == 1 or self._underruns % 20 == 0:
                    app_signals.call_status.emit(f"Relay buffering ({self._underruns})")
                self._output.write(silence)
            except Exception as exc:
                app_signals.call_status.emit(f"Relay output error: {exc}")
                time.sleep(0.1)


class RelayVideoSession:
    def __init__(self, peer, session_id):
        import cv2

        self.peer = peer
        self.session_id = session_id
        self._cv2 = cv2
        self._stop = threading.Event()
        self._http = requests.Session()
        self._seq = 0
        self._fps = float(os.environ.get("CHAT_VIDEO_FPS", "4"))
        self._quality = int(os.environ.get("CHAT_VIDEO_QUALITY", "45"))
        self._width = int(os.environ.get("CHAT_VIDEO_WIDTH", "320"))
        self._camera_index = int(os.environ.get("CHAT_VIDEO_CAMERA", "0"))
        self._capture = cv2.VideoCapture(self._camera_index)
        if not self._capture.isOpened():
            raise RuntimeError(f"camera {self._camera_index} did not open")
        self._capture.set(cv2.CAP_PROP_FRAME_WIDTH, self._width)
        self._capture.set(cv2.CAP_PROP_FRAME_HEIGHT, int(self._width * 0.75))

    def start(self):
        threading.Thread(target=self._send_loop, daemon=True).start()
        threading.Thread(target=self._receive_loop, daemon=True).start()
        app_signals.call_status.emit("Relay video active")

    def stop(self):
        self._stop.set()
        try:
            self._capture.release()
        except Exception:
            pass

    def _send_loop(self):
        delay = max(0.1, 1.0 / max(1.0, self._fps))
        while not self._stop.is_set():
            ok, frame = self._capture.read()
            if ok:
                try:
                    height, width = frame.shape[:2]
                    if width > self._width:
                        scale = self._width / width
                        frame = self._cv2.resize(frame, (self._width, int(height * scale)))
                    ok, encoded = self._cv2.imencode(
                        ".jpg",
                        frame,
                        [int(self._cv2.IMWRITE_JPEG_QUALITY), self._quality],
                    )
                    if ok:
                        self._seq += 1
                        self._http.post(
                            BASE_URL + "/relay_video_send",
                            json={
                                "username": g_username,
                                "password": g_password,
                                "target": self.peer,
                                "session_id": self.session_id,
                                "image": base64.b64encode(encoded.tobytes()).decode("ascii"),
                                "seq": self._seq,
                            },
                            timeout=4,
                        )
                except Exception as exc:
                    app_signals.call_status.emit(f"Video send error: {exc}")
            time.sleep(delay)

    def _receive_loop(self):
        frames = 0
        while not self._stop.is_set():
            try:
                response = self._http.get(
                    BASE_URL + f"/relay_video_poll?username={quote(g_username)}&session_id={quote(self.session_id)}",
                    timeout=4,
                )
                data = response.json()
            except Exception:
                data = None
            if isinstance(data, dict):
                frames_in = sorted(data.get("frames", []), key=lambda item: item.get("seq", 0))
                if frames_in:
                    latest = frames_in[-1]
                    try:
                        image = base64.b64decode(latest.get("image", ""))
                        app_signals.video_frame.emit(image)
                        frames += 1
                        if frames == 1 or frames % 20 == 0:
                            app_signals.call_status.emit(f"Relay video frames: {frames}")
                    except Exception as exc:
                        app_signals.call_status.emit(f"Video receive error: {exc}")
            time.sleep(0.12)


# ---------------- HTTP HELPERS ----------------


def http_post(endpoint, data):
    try:
        r = requests.post(BASE_URL + endpoint, json=data, timeout=8)
        return r.json() if r.content else {}
    except Exception as exc:
        return {"error": str(exc)}


def http_get(endpoint):
    try:
        return requests.get(BASE_URL + endpoint, timeout=8).json()
    except Exception:
        return None


def safe_profile(username, profile=None):
    if isinstance(profile, dict):
        username = profile.get("username") or username
        g_profiles[username] = {
            "username": username,
            "display_name": profile.get("display_name") or username,
            "name_color": profile.get("name_color") or "#4a9eff",
            "profile_picture": profile.get("profile_picture") or "",
        }
    result = g_profiles.get(
        username,
        {
            "username": username,
            "display_name": username,
            "name_color": "#4a9eff",
            "profile_picture": "",
        },
    )
    if username and username not in {g_username, "SYSTEM"}:
        old = g_contacts.get(username, {})
        g_contacts[username] = {**old, **result}
    return result


def load_contacts():
    global g_contacts
    try:
        with open(CONTACTS_FILE, "r", encoding="utf-8") as handle:
            data = json.load(handle)
        if isinstance(data, dict):
            g_contacts = data
            for username, profile in data.items():
                safe_profile(username, profile)
    except (OSError, ValueError, TypeError):
        g_contacts = {}


def save_contacts():
    try:
        os.makedirs(APP_DATA_DIR, exist_ok=True)
        with open(CONTACTS_FILE, "w", encoding="utf-8") as handle:
            json.dump(g_contacts, handle, indent=2)
    except OSError:
        pass


def data_url_from_file(path):
    mime = mimetypes.guess_type(path)[0] or "image/png"
    with open(path, "rb") as f:
        encoded = base64.b64encode(f.read()).decode("ascii")
    return f"data:{mime};base64,{encoded}"


def contact_image(picture, size=36):
    if Image is None:
        return None
    try:
        if picture.startswith("data:image/"):
            _, encoded = picture.split(",", 1)
            image = Image.open(io.BytesIO(base64.b64decode(encoded))).convert("RGBA")
        elif picture.startswith(("http://", "https://")):
            response = requests.get(picture, timeout=5)
            image = Image.open(io.BytesIO(response.content)).convert("RGBA")
        else:
            raise ValueError
    except Exception:
        image = Image.new("RGBA", (size, size), "#5865f2")
        draw = ImageDraw.Draw(image)
        draw.ellipse((0, 0, size - 1, size - 1), fill="#5865f2")
    image = ImageOps.fit(image, (size, size))
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size - 1, size - 1), fill=255)
    image.putalpha(mask)
    return ctk.CTkImage(light_image=image, dark_image=image, size=(size, size))


def desktop_notify(title, body):
    body = (body or "New message")[:220]
    if IS_WINDOWS:
        try:
            from winotify import Notification

            Notification(app_id="Global Chat", title=title, msg=body, duration="short").show()
            return
        except Exception:
            pass
    try:
        from plyer import notification

        notification.notify(title=title, message=body, app_name="Global Chat", timeout=6)
        return
    except Exception:
        pass
    if sys.platform.startswith("linux"):
        try:
            subprocess.Popen(
                ["notify-send", "--app-name=Global Chat", title, body],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
            )
        except OSError:
            pass


YOUTUBE_RE = re.compile(
    r"(https?://(?:www\.)?(?:youtube\.com/watch\?v=|youtu\.be/|youtube\.com/shorts/)([A-Za-z0-9_-]{6,}))"
)


def markdown_to_html(text):
    try:
        import markdown

        return markdown.markdown(
            text,
            extensions=["extra", "sane_lists", "nl2br"],
            output_format="html5",
        )
    except Exception:
        escaped = html.escape(text)
        escaped = re.sub(r"`([^`]+)`", r"<code>\1</code>", escaped)
        escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
        escaped = re.sub(r"\*([^*]+)\*", r"<em>\1</em>", escaped)
        escaped = re.sub(
            r"\[([^\]]+)\]\((https?://[^)\s]+)\)",
            r'<a href="\2">\1</a>',
            escaped,
        )
        escaped = re.sub(
            r"(https?://[^\s<]+)",
            r'<a href="\1">\1</a>',
            escaped,
        )
        return escaped.replace("\n", "<br>")


def youtube_blocks(text):
    blocks = []
    seen = set()
    for match in YOUTUBE_RE.finditer(text):
        video_id = match.group(2)
        if video_id in seen:
            continue
        seen.add(video_id)
        thumb = f"https://img.youtube.com/vi/{video_id}/hqdefault.jpg"
        blocks.append(
            "<div style='margin-top:8px;'>"
            f"<a href='yt:{video_id}'>"
            f"<img src='{thumb}' width='320' height='180'><br>"
            "Play embedded YouTube video"
            "</a></div>"
        )
    return "".join(blocks)


def attachment_html(attachment):
    if not isinstance(attachment, dict):
        return ""
    if not attachment.get("id") or not attachment.get("url"):
        return ""
    filename = html.escape(attachment.get("filename") or "download")
    size = attachment.get("size") or 0
    url = urljoin(BASE_URL + "/", attachment.get("url", "").lstrip("/"))
    return (
        "<div style='margin-top:8px; padding:8px; border:1px solid #444;'>"
        f"File: <a href='filedl:{html.escape(url)}'>{filename}</a> "
        f"<span style='color:#999999'>({size:,} bytes)</span>"
        "</div>"
    )


def inline_markdown_html(text):
    body = markdown_to_html(text)
    body = re.sub(r"^\s*<p>(.*)</p>\s*$", r"\1", body, flags=re.DOTALL)
    body = body.replace("<p>", "").replace("</p>", "<br>")
    return body


def render_message_html(message):
    sender = message.get("sender", "")
    text = message.get("text", "")
    is_system = message.get("is_system", False)
    profile = safe_profile(sender, message.get("profile") or {})

    if is_system:
        return f"<div style='margin-bottom:6px; color:#999999'>&gt;&gt; {html.escape(text)}</div>"

    name = html.escape(profile["display_name"])
    color = html.escape(profile["name_color"])
    body = inline_markdown_html(text)
    video = youtube_blocks(text)
    file_block = attachment_html(message.get("attachment") or {})
    return (
        "<div style='margin-bottom:10px;'>"
        f"<span style='white-space:nowrap'><b style='color:{color}'>[{name}]</b> "
        f"<span style='color:#dddddd'>{body}</span></span>"
        f"{video}{file_block}</div>"
    )


# ---------------- THREAD-SAFE UI EVENTS ----------------


class EventSignal:
    def __init__(self):
        self.callbacks = []

    def connect(self, callback):
        self.callbacks.append(callback)

    def emit(self, *args):
        UI_EVENTS.put((self, args))


class AppSignals:
    def __init__(self):
        self.new_message = EventSignal()
        self.dm_message = EventSignal()
        self.history_batch = EventSignal()
        self.login_result = EventSignal()
        self.users_updated = EventSignal()
        self.incoming_call = EventSignal()
        self.call_status = EventSignal()
        self.video_frame = EventSignal()


UI_EVENTS = queue.Queue()
app_signals = AppSignals()


# ---------------- WEBRTC ----------------


def _new_peer_connection():
    return RTCPeerConnection(
        RTCConfiguration(
            iceServers=[
                RTCIceServer(urls=["stun:stun.l.google.com:19302"]),
                RTCIceServer(urls=["stun:stun1.l.google.com:19302"]),
            ]
        )
    )


async def _wait_for_ice_gathering(pc, timeout=3):
    if pc.iceGatheringState == "complete":
        return
    done = asyncio.Event()

    @pc.on("icegatheringstatechange")
    async def on_icegatheringstatechange():
        app_signals.call_status.emit(f"ICE gathering {pc.iceGatheringState}")
        if pc.iceGatheringState == "complete":
            done.set()

    try:
        await asyncio.wait_for(done.wait(), timeout=timeout)
    except asyncio.TimeoutError:
        app_signals.call_status.emit(f"ICE gathering continuing ({pc.iceGatheringState})")


def _webrtc_thread():
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    with g_call_lock:
        g_call["loop"] = loop
    loop.run_forever()


def _add_microphone_track(pc):
    errors = []
    with g_call_lock:
        g_call["mic_error"] = ""

    try:
        import sounddevice as sd

        device_name = _sounddevice_env_device()
        sample_rates = [48000]
        try:
            query_target = device_name if device_name is not None else sd.default.device[0]
            info = sd.query_devices(query_target, "input")
            default_rate = int(info.get("default_samplerate") or 0)
            if default_rate and default_rate not in sample_rates:
                sample_rates.append(default_rate)
        except Exception as exc:
            errors.append(f"sounddevice query failed: {exc}")

        for sample_rate in sample_rates:
            try:
                track = SoundDeviceMicrophoneTrack(device=device_name, samplerate=sample_rate)
                pc.addTrack(track)
                app_signals.call_status.emit(
                    f"Mic active via sounddevice{f': {device_name}' if device_name is not None else ''} @ {sample_rate} Hz"
                )
                return True
            except Exception as exc:
                errors.append(f"sounddevice mic {sample_rate} Hz failed: {exc}")
    except Exception as exc:
        errors.append(f"sounddevice mic setup failed: {exc}")

    try:
        from aiortc.contrib.media import MediaPlayer

        if IS_WINDOWS:
            candidates = []
            if os.environ.get("CHAT_DSHOW_DEVICE"):
                candidates.append(os.environ["CHAT_DSHOW_DEVICE"])
            if os.environ.get("CHAT_AUDIO_DEVICE", "").startswith("audio="):
                candidates.append(os.environ["CHAT_AUDIO_DEVICE"])
            candidates.extend(["audio=Microphone", "audio=Microphone Array", "audio=default"])

            player = None
            device = candidates[0]
            for candidate in dict.fromkeys(candidates):
                try:
                    device = candidate
                    player = MediaPlayer(candidate, format="dshow", options={"rtbufsize": "100M"})
                    if player.audio:
                        break
                except Exception as exc:
                    errors.append(f"dshow {candidate} failed: {exc}")
                    player = None
            if player is None:
                raise RuntimeError("no Windows microphone opened")
        elif sys.platform == "darwin":
            device = os.environ.get("CHAT_AUDIO_DEVICE", "default")
            player = MediaPlayer(device, format="avfoundation")
        else:
            device = os.environ.get("CHAT_AUDIO_DEVICE", "default")
            player = None
            for fmt in ("pulse", "alsa"):
                try:
                    player = MediaPlayer(device, format=fmt)
                    if player.audio:
                        app_signals.call_status.emit(f"Mic active via {fmt}: {device}")
                        break
                except Exception as exc:
                    errors.append(f"{fmt} mic failed: {exc}")
                    player = None
            if player is None:
                raise RuntimeError("; ".join(errors) or "no Linux mic backend opened")

        if player.audio:
            pc.addTrack(player.audio)
            if IS_WINDOWS:
                app_signals.call_status.emit(f"Mic active via dshow: {device}")
            elif sys.platform == "darwin":
                app_signals.call_status.emit(f"Mic active via avfoundation: {device}")
            return True
    except Exception as exc:
        errors.append(str(exc))

    if errors:
        detail = "; ".join(errors)
        detail = f"{_sounddevice_input_summary()}; {detail}"
        with g_call_lock:
            g_call["mic_error"] = detail
        app_signals.call_status.emit(f"Mic error: {detail[:220]}")
    return False


def _ensure_audio_receive(pc, has_microphone):
    if has_microphone:
        return
    try:
        pc.addTransceiver("audio", direction="recvonly")
        with g_call_lock:
            detail = g_call.get("mic_error", "")
        if detail:
            app_signals.call_status.emit(f"Mic unavailable: {detail[:260]}")
        else:
            app_signals.call_status.emit("Mic unavailable: no specific error was reported")
    except Exception as exc:
        app_signals.call_status.emit(f"Audio setup failed: {exc}")


def _wire_ice_sender(pc, peer, sid):
    @pc.on("icecandidate")
    async def on_icecandidate(candidate):
        if candidate is None:
            return
        try:
            http_post(
                "/webrtc_ice",
                {
                    "target": peer,
                    "candidate": candidate_to_sdp(candidate),
                    "sdp_mline_index": candidate.sdpMLineIndex,
                    "sdp_mid": candidate.sdpMid,
                    "session_id": sid,
                },
            )
        except Exception:
            pass


async def _apply_remote_ice(pc, candidates):
    for item in candidates or []:
        try:
            candidate_text = item.get("candidate")
            if not candidate_text:
                continue
            candidate = candidate_from_sdp(candidate_text)
            candidate.sdpMLineIndex = item.get("sdp_mline_index", 0)
            candidate.sdpMid = item.get("sdp_mid")
            await pc.addIceCandidate(candidate)
        except Exception as exc:
            app_signals.call_status.emit(f"ICE error: {exc}")


async def _poll_active_call_signaling(pc, peer, sid):
    while True:
        await asyncio.sleep(1)
        with g_call_lock:
            if not g_call["active"] or g_call["session_id"] != sid:
                return
        data = http_get(f"/webrtc_poll?username={quote(g_username)}&session_id={quote(sid)}")
        if not isinstance(data, dict):
            continue
        await _apply_remote_ice(pc, data.get("ice"))
        for status in data.get("status", []):
            state = status.get("state")
            if state == "ended":
                app_signals.call_status.emit("Call ended")
                await _do_end_call(notify_peer=False)
                return
            if state == "rejected":
                app_signals.call_status.emit("Call rejected")
                await _do_end_call(notify_peer=False)
                return


def _wire_call_events(pc):
    @pc.on("connectionstatechange")
    async def on_connectionstatechange():
        app_signals.call_status.emit(f"Call {pc.connectionState}")

    @pc.on("iceconnectionstatechange")
    async def on_iceconnectionstatechange():
        app_signals.call_status.emit(f"ICE {pc.iceConnectionState}")
        if pc.iceConnectionState in {"failed", "disconnected"}:
            app_signals.call_status.emit("ICE failed: this network may need a TURN server")

    @pc.on("track")
    def on_track(track):
        if track.kind == "audio":
            app_signals.call_status.emit("Receiving audio")
            task = asyncio.ensure_future(_play_remote_audio(track))
            with g_call_lock:
                g_call["audio_players"].append(task)


def _start_relay_audio(peer, sid):
    with g_call_lock:
        existing = g_call.get("relay")
    if existing:
        return
    try:
        relay = RelayAudioSession(peer, sid)
        relay.start()
        with g_call_lock:
            g_call["relay"] = relay
    except Exception as exc:
        app_signals.call_status.emit(f"Relay audio failed: {exc}")


def _stop_relay_audio():
    with g_call_lock:
        relay = g_call.get("relay")
        g_call["relay"] = None
    if relay:
        relay.stop()


def _start_relay_video(peer, sid):
    with g_call_lock:
        existing = g_call.get("video")
    if existing:
        return
    try:
        video = RelayVideoSession(peer, sid)
        video.start()
        with g_call_lock:
            g_call["video"] = video
    except ImportError:
        app_signals.call_status.emit("Install opencv-python for video")
    except Exception as exc:
        app_signals.call_status.emit(f"Relay video failed: {exc}")


def _stop_relay_video():
    with g_call_lock:
        video = g_call.get("video")
        g_call["video"] = None
    if video:
        video.stop()


async def _play_remote_audio(track):
    player = RemoteAudioPlayer()
    if not player.available:
        app_signals.call_status.emit(player._last_error or "Install sounddevice or pyaudio to hear calls")
        while True:
            await track.recv()
        return
    frames_received = 0
    try:
        while True:
            frame = await track.recv()
            frames_received += 1
            if frames_received == 1 or frames_received % 50 == 0:
                app_signals.call_status.emit(f"Remote audio frames: {frames_received}")
            player.write_frame(frame)
    except Exception as exc:
        app_signals.call_status.emit(f"Audio stopped: {exc}")
    finally:
        player.close()


async def _do_call_caller(callee, sid):
    pc = _new_peer_connection()
    _wire_call_events(pc)
    _wire_ice_sender(pc, callee, sid)
    has_microphone = _add_microphone_track(pc)
    _ensure_audio_receive(pc, has_microphone)
    with g_call_lock:
        g_call["pc"] = pc

    offer = await pc.createOffer()
    await pc.setLocalDescription(offer)
    await _wait_for_ice_gathering(pc)
    http_post(
        "/webrtc_offer",
        {
            "caller": g_username,
            "callee": callee,
            "sdp": pc.localDescription.sdp,
            "session_id": sid,
        },
    )
    app_signals.call_status.emit("Ringing...")

    for _ in range(90):
        await asyncio.sleep(1)
        d = http_get(f"/webrtc_poll?username={quote(g_username)}&session_id={quote(sid)}")
        if not isinstance(d, dict):
            continue
        for status in d.get("status", []):
            state = status.get("state")
            if state == "rejected":
                app_signals.call_status.emit("Call rejected")
                await _do_end_call(notify_peer=False)
                return
            if state == "ended":
                app_signals.call_status.emit("Call ended")
                await _do_end_call(notify_peer=False)
                return
        if d.get("answers"):
            answer = d["answers"][0]
            await pc.setRemoteDescription(RTCSessionDescription(sdp=answer["sdp"], type="answer"))
            await _apply_remote_ice(pc, d.get("ice"))
            asyncio.ensure_future(_poll_active_call_signaling(pc, callee, sid))
            _start_relay_audio(callee, sid)
            _start_relay_video(callee, sid)
            app_signals.call_status.emit("Answer received; connecting media")
            return

    app_signals.call_status.emit("No answer")
    await _do_end_call()


async def _do_call_callee(caller, sdp, sid, pending_ice=None):
    pc = _new_peer_connection()
    _wire_call_events(pc)
    _wire_ice_sender(pc, caller, sid)
    has_microphone = _add_microphone_track(pc)
    _ensure_audio_receive(pc, has_microphone)
    with g_call_lock:
        g_call["pc"] = pc

    await pc.setRemoteDescription(RTCSessionDescription(sdp=sdp, type="offer"))
    await _apply_remote_ice(pc, pending_ice or [])
    answer = await pc.createAnswer()
    await pc.setLocalDescription(answer)
    await _wait_for_ice_gathering(pc)
    http_post("/webrtc_answer", {"target": caller, "sdp": pc.localDescription.sdp, "session_id": sid})
    asyncio.ensure_future(_poll_active_call_signaling(pc, caller, sid))
    _start_relay_audio(caller, sid)
    _start_relay_video(caller, sid)
    app_signals.call_status.emit("Answer sent; connecting media")


async def _do_end_call(notify_peer=True):
    _stop_relay_audio()
    _stop_relay_video()
    with g_call_lock:
        pc = g_call.get("pc")
        sid = g_call.get("session_id", "")
        peer = g_call.get("peer", "")
        tasks = list(g_call.get("audio_players", []))
        g_call["audio_players"] = []
    for task in tasks:
        task.cancel()
    if pc:
        await pc.close()
    if notify_peer and sid:
        http_post("/webrtc_end", {"session_id": sid, "peer": peer})


def start_call_caller(callee):
    with g_call_lock:
        if g_call["active"]:
            return
        sid = f"{g_username}-{callee}-{int(time.time())}"
        g_call.update({"active": True, "peer": callee, "session_id": sid})
        loop = g_call["loop"]
    threading.Thread(target=_relay_call_caller, args=(callee, sid), daemon=True).start()


def start_call_callee(caller, sdp, sid, pending_ice=None):
    with g_call_lock:
        if g_call["active"]:
            return
        g_call.update({"active": True, "peer": caller, "session_id": sid, "pending": False, "pending_ice": []})
        loop = g_call["loop"]
    threading.Thread(target=_relay_call_callee, args=(caller, sid), daemon=True).start()


def end_call(notify_peer=True):
    with g_call_lock:
        active = g_call["active"] or g_call["pc"] is not None
        loop = g_call["loop"]
    if not active:
        return
    if loop and WEBRTC:
        asyncio.run_coroutine_threadsafe(_do_end_call(notify_peer), loop)
    else:
        _stop_relay_audio()
        _stop_relay_video()
        with g_call_lock:
            sid = g_call.get("session_id", "")
            peer = g_call.get("peer", "")
        if notify_peer and sid:
            http_post("/webrtc_end", {"session_id": sid, "peer": peer})
    with g_call_lock:
        g_call.update({
            "active": False,
            "pc": None,
            "peer": "",
            "session_id": "",
            "pending": False,
            "pending_ice": [],
            "audio_players": [],
            "relay": None,
            "video": None,
        })


def _relay_call_caller(callee, sid):
    http_post("/webrtc_offer", {
        "caller": g_username, "callee": callee, "sdp": "global-chat-relay-v1", "session_id": sid,
    })
    app_signals.call_status.emit("Ringing…")
    for _ in range(90):
        time.sleep(1)
        with g_call_lock:
            if not g_call["active"] or g_call["session_id"] != sid:
                return
        data = http_get(f"/webrtc_poll?username={quote(g_username)}&session_id={quote(sid)}")
        if not isinstance(data, dict):
            continue
        for status in data.get("status", []):
            if status.get("state") in {"rejected", "ended"}:
                app_signals.call_status.emit("Call rejected" if status.get("state") == "rejected" else "Call ended")
                end_call(notify_peer=False)
                return
        if data.get("answers"):
            _start_relay_audio(callee, sid)
            _start_relay_video(callee, sid)
            app_signals.call_status.emit("Connected")
            threading.Thread(target=_poll_relay_call, args=(sid,), daemon=True).start()
            return
    app_signals.call_status.emit("No answer")
    end_call()


def _relay_call_callee(caller, sid):
    http_post("/webrtc_answer", {"target": caller, "sdp": "global-chat-relay-v1", "session_id": sid})
    _start_relay_audio(caller, sid)
    _start_relay_video(caller, sid)
    app_signals.call_status.emit("Connected")
    _poll_relay_call(sid)


def _poll_relay_call(sid):
    while True:
        time.sleep(1)
        with g_call_lock:
            if not g_call["active"] or g_call["session_id"] != sid:
                return
        data = http_get(f"/webrtc_poll?username={quote(g_username)}&session_id={quote(sid)}")
        if not isinstance(data, dict):
            continue
        if any(status.get("state") in {"ended", "rejected"} for status in data.get("status", [])):
            app_signals.call_status.emit("Call ended")
            end_call(notify_peer=False)
            return


# ---------------- CALL WINDOW ----------------

''' Legacy PyQt interface retained below for reference.
class CallWindow(QWidget):
    def __init__(self, peer):
        super().__init__()
        self.setWindowTitle("Call")
        self.setFixedSize(500, 520)
        layout = QVBoxLayout()
        layout.addWidget(QLabel(f"Call with {peer}", alignment=Qt.AlignCenter))
        self.video_lbl = QLabel("Waiting for video...", alignment=Qt.AlignCenter)
        self.video_lbl.setFixedSize(480, 360)
        self.video_lbl.setStyleSheet("background-color:#111; color:#999; border:1px solid #333;")
        layout.addWidget(self.video_lbl, alignment=Qt.AlignCenter)
        self.status_lbl = QLabel("Connecting...", alignment=Qt.AlignCenter)
        self.status_lbl.setWordWrap(True)
        layout.addWidget(self.status_lbl)
        row = QHBoxLayout()
        self.mute_btn = QPushButton("Mute Mic")
        self.mute_btn.setCheckable(True)
        test_audio = QPushButton("Test Audio")
        test_audio.clicked.connect(self._test_audio)
        hangup = QPushButton("Hang Up")
        hangup.clicked.connect(self._hangup)
        row.addWidget(self.mute_btn)
        row.addWidget(test_audio)
        row.addWidget(hangup)
        layout.addLayout(row)
        self.setLayout(layout)
        app_signals.call_status.connect(self.status_lbl.setText)
        app_signals.video_frame.connect(self._on_video_frame)

    def _hangup(self):
        end_call()
        self.close()

    def _test_audio(self):
        threading.Thread(target=self._play_test_tone, daemon=True).start()

    def _play_test_tone(self):
        player = RemoteAudioPlayer()
        if not player.available:
            app_signals.call_status.emit(player._last_error or "No audio playback backend")
            return
        try:
            samples = []
            for index in range(48000 // 3):
                value = int(9000 * math.sin(2 * math.pi * 660 * (index / 48000)))
                samples.append(struct.pack("<hh", value, value))
            player.write_pcm(b"".join(samples))
            app_signals.call_status.emit("Speaker test played")
        except Exception as exc:
            app_signals.call_status.emit(f"Speaker test failed: {exc}")
        finally:
            player.close()

    def _on_video_frame(self, image_bytes):
        image = QImage.fromData(image_bytes, "JPG")
        if image.isNull():
            return
        pixmap = QPixmap.fromImage(image).scaled(
            self.video_lbl.size(),
            Qt.KeepAspectRatio,
            Qt.SmoothTransformation,
        )
        self.video_lbl.setPixmap(pixmap)

    def closeEvent(self, event):
        end_call()
        event.accept()


# ---------------- CHAT WINDOW ----------------


class ChatWindow(QWidget):
    def __init__(self):
        super().__init__()
        global g_last_id, g_last_dm_id, g_current_dm
        g_last_id = -1
        g_last_dm_id = -1
        g_current_dm = ""
        self._call_win = None
        self._messages = []
        self._message_ids = set()
        self._oldest_id = None
        self._view_token = 0
        self.setWindowTitle(f"Chat - {platform.system()} {platform.release()}")
        self.resize(900, 580)
        self._build_ui()
        app_signals.new_message.connect(self._on_message)
        app_signals.history_batch.connect(self._on_history_batch)
        app_signals.users_updated.connect(self._on_users)
        app_signals.incoming_call.connect(self._on_incoming_call)
        app_signals.call_status.connect(self._on_call_status)
        self._load_recent_history()
        self._start_polling()

    def _build_ui(self):
        main = QHBoxLayout()

        left = QVBoxLayout()
        self.user_list = QListWidget()
        self.user_list.setFixedWidth(210)
        self.user_list.setIconSize(QSize(32, 32))
        self.user_list.itemClicked.connect(self._open_dm)
        self.user_list.currentItemChanged.connect(self._sel_changed)
        left.addWidget(self.user_list)

        profile_btn = QPushButton("Edit Profile")
        profile_btn.clicked.connect(self._edit_profile)
        left.addWidget(profile_btn)
        main.addLayout(left)

        right = QVBoxLayout()
        top = QHBoxLayout()
        glob_btn = QPushButton("Global")
        glob_btn.clicked.connect(self._open_global)
        older_btn = QPushButton("Load Older")
        older_btn.clicked.connect(self._load_older_history)
        self.title_lbl = QLabel("Global Chat")
        top.addWidget(glob_btn)
        top.addWidget(older_btn)
        top.addWidget(self.title_lbl, 1)
        right.addLayout(top)

        self.chat = QTextBrowser()
        self.chat.setReadOnly(True)
        self.chat.setOpenExternalLinks(False)
        self.chat.anchorClicked.connect(self._open_chat_link)
        right.addWidget(self.chat)

        bottom = QHBoxLayout()
        self.msg_input = QLineEdit()
        self.msg_input.returnPressed.connect(self._send)
        send_btn = QPushButton("Send")
        send_btn.clicked.connect(self._send)
        attach_btn = QPushButton("Attach")
        attach_btn.clicked.connect(self._attach_file)
        self.call_btn = QPushButton("Call")
        self.call_btn.setFixedWidth(78)
        self.call_btn.setEnabled(False)
        self.call_btn.clicked.connect(self._call_clicked)
        bottom.addWidget(self.msg_input)
        bottom.addWidget(attach_btn)
        bottom.addWidget(send_btn)
        bottom.addWidget(self.call_btn)
        right.addLayout(bottom)

        main.addLayout(right)
        self.setLayout(main)

    def _open_global(self):
        global g_current_dm, g_last_id
        with g_dm_lock:
            g_current_dm = ""
        g_last_id = -1
        self._reset_chat_view()
        self.title_lbl.setText("Global Chat")
        self.call_btn.setEnabled(False)
        self._load_recent_history()

    def _open_dm(self, item):
        global g_current_dm, g_last_dm_id
        name = item.data(Qt.UserRole) or item.text()
        with g_dm_lock:
            g_current_dm = name
        g_last_dm_id = -1
        self._reset_chat_view()
        profile = safe_profile(name)
        self.title_lbl.setText(f"DM with {profile['display_name']}")
        self.call_btn.setEnabled(True)
        self._load_recent_history()

    def _sel_changed(self, current, _):
        with g_call_lock:
            active = g_call["active"]
        self.call_btn.setEnabled(current is not None and not active)

    def _reset_chat_view(self):
        self._view_token += 1
        self._messages = []
        self._message_ids = set()
        self._oldest_id = None
        self.chat.clear()

    def _history_endpoint(self, before=None):
        with g_dm_lock:
            target = g_current_dm
        if target:
            endpoint = f"/dm_messages?user={quote(g_username)}&with={quote(target)}&limit=100"
        else:
            endpoint = "/messages?limit=100"
        if before is not None:
            endpoint += f"&before={before}"
        return endpoint

    def _load_recent_history(self):
        token = self._view_token
        threading.Thread(target=self._fetch_history, args=(token, None, False), daemon=True).start()

    def _load_older_history(self):
        if self._oldest_id is None:
            return
        token = self._view_token
        threading.Thread(target=self._fetch_history, args=(token, self._oldest_id, True), daemon=True).start()

    def _fetch_history(self, token, before, prepend):
        data = http_get(self._history_endpoint(before))
        if token != self._view_token or not isinstance(data, list):
            return
        messages = []
        for msg in data:
            sender = msg.get("sender", msg.get("username", ""))
            messages.append(
                {
                    "id": msg.get("id", 0),
                    "sender": sender,
                    "text": msg.get("message", ""),
                    "is_system": sender == "SYSTEM",
                    "profile": msg.get("profile") or {},
                    "attachment": msg.get("attachment") or {},
                }
            )
        app_signals.history_batch.emit(messages, prepend)

    def _on_history_batch(self, messages, prepend):
        added = []
        for message in messages:
            mid = message.get("id", 0)
            if mid in self._message_ids:
                continue
            self._message_ids.add(mid)
            added.append(message)

        if prepend:
            self._messages = added + self._messages
        else:
            self._messages.extend(added)

        ids = [m.get("id", 0) for m in self._messages if m.get("id", 0)]
        if ids:
            self._oldest_id = min(ids)
            self._sync_last_ids(max(ids))
        self._render_chat(scroll_to_bottom=not prepend)

    def _sync_last_ids(self, latest_id):
        global g_last_id, g_last_dm_id
        with g_dm_lock:
            target = g_current_dm
        if target:
            g_last_dm_id = max(g_last_dm_id, latest_id)
        else:
            g_last_id = max(g_last_id, latest_id)

    def _render_chat(self, scroll_to_bottom=True):
        old_scroll = self.chat.verticalScrollBar().value()
        self.chat.clear()
        self.chat.setHtml("<br>".join(render_message_html(message) for message in self._messages))
        if scroll_to_bottom:
            bar = self.chat.verticalScrollBar()
            bar.setValue(bar.maximum())
        elif old_scroll > 0:
            self.chat.verticalScrollBar().setValue(old_scroll)

    def _send(self):
        msg = self.msg_input.text().strip()
        if not msg:
            return
        self.msg_input.clear()
        self._send_message(msg)

    def _send_message(self, msg, attachment_id=None):
        with g_dm_lock:
            target = g_current_dm
        if not target:
            payload = {
                "username": g_username,
                "password": g_password,
                "message": msg,
                "attachment_id": attachment_id,
            }
            threading.Thread(target=http_post, args=("/send", payload), daemon=True).start()
        else:
            payload = {
                "username": g_username,
                "password": g_password,
                "to": target,
                "message": msg,
                "attachment_id": attachment_id,
            }
            threading.Thread(target=http_post, args=("/dm_send", payload), daemon=True).start()

    def _attach_file(self):
        path, _ = QFileDialog.getOpenFileName(self, "Choose file to upload", "")
        if not path:
            return
        try:
            size = os.path.getsize(path)
            if size > 15 * 1024 * 1024:
                QMessageBox.warning(self, "File too large", "Choose a file under 15 MB.")
                return
            with open(path, "rb") as f:
                encoded = base64.b64encode(f.read()).decode("ascii")
            payload = {
                "username": g_username,
                "password": g_password,
                "filename": os.path.basename(path),
                "mime_type": mimetypes.guess_type(path)[0] or "application/octet-stream",
                "data": encoded,
            }
            result = http_post("/upload", payload)
            if isinstance(result, dict) and result.get("attachment"):
                caption = self.msg_input.text().strip()
                self.msg_input.clear()
                self._send_message(caption, result["attachment"]["id"])
            else:
                QMessageBox.warning(self, "Upload failed", (result or {}).get("error", "Could not upload file."))
        except Exception as exc:
            QMessageBox.warning(self, "Upload failed", str(exc))

    def _call_clicked(self):
        with g_call_lock:
            active = g_call["active"]
        if active:
            end_call()
            self.call_btn.setText("Call")
            if self._call_win:
                self._call_win.close()
                self._call_win = None
            return

        with g_dm_lock:
            target = g_current_dm
        if not target:
            return
        if not WEBRTC:
            QMessageBox.information(self, "Calls unavailable", "Install call support with:\n  pip install aiortc av")
            return
        self.call_btn.setText("Hang Up")
        self._call_win = CallWindow(safe_profile(target)["display_name"])
        self._call_win.show()
        threading.Thread(target=start_call_caller, args=(target,), daemon=True).start()

    def _on_incoming_call(self, caller):
        profile = safe_profile(caller)
        reply = QMessageBox.question(
            self,
            "Incoming Call",
            f"Incoming call from {profile['display_name']}\nAccept?",
            QMessageBox.Yes | QMessageBox.No,
        )
        with g_call_lock:
            sdp = g_call["pending_sdp"]
            sid = g_call["pending_sid"]
            pending_ice = list(g_call.get("pending_ice", []))
        if reply == QMessageBox.Yes:
            self.call_btn.setText("Hang Up")
            self._call_win = CallWindow(profile["display_name"])
            self._call_win.show()
            threading.Thread(target=start_call_callee, args=(caller, sdp, sid, pending_ice), daemon=True).start()
        else:
            http_post("/webrtc_reject", {"target": caller, "session_id": sid})
            with g_call_lock:
                g_call["pending"] = False
                g_call["pending_ice"] = []

    def _on_call_status(self, status):
        if status in {"Call rejected", "Call ended", "No answer"}:
            self.call_btn.setText("Call")
            if self._call_win:
                self._call_win.status_lbl.setText(status)

    def _on_message(self, message_id, sender, text, is_system, profile, attachment):
        if message_id in self._message_ids:
            return
        self._message_ids.add(message_id)
        message = {
            "id": message_id,
            "sender": sender,
            "text": text,
            "is_system": is_system,
            "profile": profile,
            "attachment": attachment,
        }
        self._messages.append(message)
        if self._oldest_id is None or message_id < self._oldest_id:
            self._oldest_id = message_id
        self.chat.append(render_message_html(message))
        self.chat.ensureCursorVisible()

    def _open_chat_link(self, url):
        link = url.toString()
        if link.startswith("filedl:"):
            QDesktopServices.openUrl(QUrl(link[len("filedl:") :]))
        elif link.startswith("yt:"):
            self._open_youtube_embed(link[len("yt:") :])
        else:
            QDesktopServices.openUrl(url)

    def _open_youtube_embed(self, video_id):
        embed_url = f"https://www.youtube.com/embed/{video_id}?autoplay=1"
        try:
            from PyQt5.QtWebEngineWidgets import QWebEngineView

            win = QWidget(self)
            win.setWindowTitle("YouTube")
            win.resize(820, 520)
            layout = QVBoxLayout()
            view = QWebEngineView()
            view.setUrl(QUrl(embed_url))
            layout.addWidget(view)
            win.setLayout(layout)
            win.show()
            self._youtube_window = win
        except Exception:
            webbrowser.open(embed_url)

    def _on_users(self, user_list):
        current = None
        item = self.user_list.currentItem()
        if item:
            current = item.data(Qt.UserRole)

        self.user_list.clear()
        for user in user_list:
            if isinstance(user, str):
                username = user
                profile = safe_profile(username)
            else:
                username = user.get("username", "")
                profile = safe_profile(username, user)
            if not username or username == g_username:
                continue

            entry = QListWidgetItem(profile["display_name"])
            entry.setData(Qt.UserRole, username)
            entry.setToolTip(username)
            entry.setForeground(QColor(profile["name_color"]))
            entry.setIcon(QIcon(pixmap_from_picture(profile["profile_picture"])))
            self.user_list.addItem(entry)
            if current == username:
                self.user_list.setCurrentItem(entry)

    def _edit_profile(self):
        profile = safe_profile(g_username)
        name = self._ask_name(profile["display_name"])
        if name is None:
            return
        color = QColorDialog.getColor(QColor(profile["name_color"]), self, "Choose name color")
        if not color.isValid():
            return

        picture = profile["profile_picture"]
        reply = QMessageBox.question(
            self,
            "Profile Picture",
            "Choose a new profile picture?",
            QMessageBox.Yes | QMessageBox.No,
        )
        if reply == QMessageBox.Yes:
            path, _ = QFileDialog.getOpenFileName(
                self,
                "Choose profile picture",
                "",
                "Images (*.png *.jpg *.jpeg *.gif *.webp)",
            )
            if path:
                try:
                    if os.path.getsize(path) > 450000:
                        QMessageBox.warning(self, "Picture too large", "Choose an image under 450 KB.")
                        return
                    picture = data_url_from_file(path)
                except Exception as exc:
                    QMessageBox.warning(self, "Picture error", str(exc))
                    return

        result = http_post(
            "/profile",
            {
                "username": g_username,
                "password": g_password,
                "display_name": name,
                "name_color": color.name(),
                "profile_picture": picture,
            },
        )
        if isinstance(result, dict) and result.get("profile"):
            safe_profile(g_username, result["profile"])
        elif isinstance(result, dict) and result.get("error"):
            QMessageBox.warning(self, "Profile error", result["error"])

    def _ask_name(self, current):
        name, ok = QInputCompat.get_text(self, "Display Name", "Name:", current)
        return name.strip()[:40] if ok and name.strip() else None

    def _start_polling(self):
        threading.Thread(target=self._poll_messages, daemon=True).start()
        threading.Thread(target=self._poll_users, daemon=True).start()
        threading.Thread(target=self._heartbeat, daemon=True).start()
        if WEBRTC:
            threading.Thread(target=self._poll_webrtc, daemon=True).start()

    def _poll_messages(self):
        global g_last_id, g_last_dm_id
        while True:
            try:
                with g_dm_lock:
                    target = g_current_dm
                if not target:
                    data = http_get(f"/messages?after={g_last_id}")
                    if isinstance(data, list):
                        for msg in data:
                            mid = msg.get("id", 0)
                            sender = msg.get("username", "")
                            if mid > g_last_id:
                                g_last_id = mid
                                app_signals.new_message.emit(
                                    mid,
                                    sender,
                                    msg.get("message", ""),
                                    sender == "SYSTEM",
                                    msg.get("profile") or {},
                                    msg.get("attachment") or {},
                                )
                else:
                    endpoint = f"/dm_messages?user={quote(g_username)}&with={quote(target)}&after={g_last_dm_id}"
                    data = http_get(endpoint)
                    if isinstance(data, list):
                        for msg in data:
                            mid = msg.get("id", 0)
                            sender = msg.get("sender", msg.get("username", ""))
                            if mid > g_last_dm_id:
                                g_last_dm_id = mid
                                app_signals.new_message.emit(
                                    mid,
                                    sender,
                                    msg.get("message", ""),
                                    False,
                                    msg.get("profile") or {},
                                    msg.get("attachment") or {},
                                )
            except Exception:
                pass
            time.sleep(0.8)

    def _poll_users(self):
        while True:
            try:
                data = http_get("/who")
                if isinstance(data, list):
                    app_signals.users_updated.emit(data)
            except Exception:
                pass
            time.sleep(2)

    def _heartbeat(self):
        while True:
            http_post("/heartbeat", {"username": g_username, "password": g_password})
            time.sleep(12)

    def _poll_webrtc(self):
        while True:
            try:
                with g_call_lock:
                    active = g_call["active"]
                    pending = g_call["pending"]
                if active:
                    time.sleep(1)
                    continue
                endpoint = f"/webrtc_poll?username={quote(g_username)}"
                data = http_get(endpoint)
                if not isinstance(data, dict):
                    time.sleep(1)
                    continue

                if not active and not pending and data.get("offers"):
                    offer = data["offers"][0]
                    caller = offer["caller"]
                    safe_profile(caller, offer.get("profile"))
                    with g_call_lock:
                        g_call["pending"] = True
                        g_call["pending_caller"] = caller
                        g_call["pending_sdp"] = offer["sdp"]
                        g_call["pending_sid"] = offer["session_id"]
                        g_call["pending_ice"] = data.get("ice") or []
                    app_signals.incoming_call.emit(caller)
            except Exception:
                pass
            time.sleep(1)

    def closeEvent(self, event):
        http_post("/leave", {"username": g_username})
        event.accept()


class QInputCompat:
    @staticmethod
    def get_text(parent, title, label, text):
        from PyQt5.QtWidgets import QInputDialog

        return QInputDialog.getText(parent, title, label, QLineEdit.Normal, text)


# ---------------- LOGIN WINDOW ----------------


class LoginWindow(QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Login")
        self.setFixedSize(300, 210)
        layout = QVBoxLayout()
        layout.addWidget(QLabel("Username"))
        self.user_in = QLineEdit()
        layout.addWidget(self.user_in)
        layout.addWidget(QLabel("Password"))
        self.pass_in = QLineEdit()
        self.pass_in.setEchoMode(QLineEdit.Password)
        layout.addWidget(self.pass_in)
        self.status = QLabel("")
        self.status.setStyleSheet("color: #f77;")
        btn = QPushButton("Login / Register")
        btn.clicked.connect(self._login)
        self.user_in.returnPressed.connect(self._login)
        self.pass_in.returnPressed.connect(self._login)
        layout.addWidget(btn)
        layout.addWidget(self.status)
        self.setLayout(layout)

    def _login(self):
        global g_username, g_password
        g_username = self.user_in.text().strip()
        g_password = self.pass_in.text()
        if not g_username or not g_password:
            self.status.setText("Username and password required")
            return
        result = http_post("/auth", {"username": g_username, "password": g_password})
        if isinstance(result, dict) and result.get("error"):
            self.status.setText(result["error"])
        else:
            if isinstance(result, dict) and result.get("profile"):
                safe_profile(g_username, result["profile"])
            chat = ChatWindow()
            chat.show()
            self.close()


# ---------------- ENTRY POINT ----------------


def main():
    app = QApplication(sys.argv)
    app.setStyleSheet(
        """
        QWidget { background-color: #1e1e1e; color: #dddddd; font-size: 13px; }
        QTextBrowser, QLineEdit { background-color: #2a2a2a; border: 1px solid #444; padding: 5px; }
        QPushButton { background-color: #3a3a3a; border: 1px solid #555; padding: 5px 10px; }
        QPushButton:hover { background-color: #484848; }
        QPushButton:pressed { background-color: #222; }
        QPushButton:disabled { color: #777; background-color: #303030; }
        QListWidget { background-color: #252525; border: 1px solid #333; }
        QListWidget::item { padding: 4px; min-height: 36px; }
        QListWidget::item:selected { background-color: #2a4a6a; }
        QScrollBar:vertical { background: #1e1e1e; width: 8px; }
        QScrollBar::handle:vertical { background: #555; border-radius: 4px; }
        """
    )

    if WEBRTC:
        thread = threading.Thread(target=_webrtc_thread, daemon=True)
        thread.start()
        time.sleep(0.15)

    login = LoginWindow()
    login.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
'''


# ---------------- CUSTOMTKINTER INTERFACE ----------------


class CallWindow(ctk.CTkToplevel):
    def __init__(self, master, peer):
        super().__init__(master)
        self.title(f"Call with {peer}")
        self.geometry("640x560")
        self.minsize(520, 460)
        self.protocol("WM_DELETE_WINDOW", self._hangup)
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        ctk.CTkLabel(self, text=f"Call with {peer}", font=ctk.CTkFont(size=20, weight="bold")).grid(
            row=0, column=0, padx=20, pady=(18, 10)
        )
        self.video = ctk.CTkLabel(self, text="Waiting for video…", fg_color="#111214", corner_radius=10)
        self.video.grid(row=1, column=0, padx=20, pady=5, sticky="nsew")
        self.status = ctk.CTkLabel(self, text="Connecting…", text_color="#b5bac1", wraplength=560)
        self.status.grid(row=2, column=0, padx=20, pady=12)
        controls = ctk.CTkFrame(self, fg_color="transparent")
        controls.grid(row=3, column=0, pady=(0, 18))
        ctk.CTkButton(controls, text="Test Audio", width=120, command=self._test_audio).pack(side="left", padx=6)
        ctk.CTkButton(
            controls, text="Hang Up", width=120, fg_color="#da373c", hover_color="#a1282d", command=self._hangup
        ).pack(side="left", padx=6)
        app_signals.call_status.connect(self._set_status)
        app_signals.video_frame.connect(self._show_video)

    def _set_status(self, text):
        if self.winfo_exists():
            self.status.configure(text=text)

    def _show_video(self, image_bytes):
        if not self.winfo_exists() or Image is None:
            return
        try:
            image = Image.open(io.BytesIO(image_bytes)).convert("RGB")
            preview = ctk.CTkImage(light_image=image, dark_image=image, size=(560, 360))
            self.video.configure(image=preview, text="")
            self.video.image = preview
        except Exception:
            pass

    def _test_audio(self):
        try:
            import numpy as np
            import sounddevice as sd

            rate = 48000
            samples = np.arange(int(rate * 0.35)) / rate
            tone = (0.12 * np.sin(2 * np.pi * 660 * samples)).astype(np.float32)
            sd.play(tone, rate)
        except Exception as exc:
            self._set_status(f"Audio test failed: {exc}")

    def _hangup(self):
        end_call()
        if self.winfo_exists():
            self.destroy()


class ChatView(ctk.CTkFrame):
    def __init__(self, master):
        super().__init__(master, fg_color="#313338")
        self.stop_event = threading.Event()
        self.view_token = 0
        self.messages = []
        self.message_ids = set()
        self.oldest_id = None
        self.dm_last_ids = {}
        self.dm_ready = set()
        self.contact_rows = {}
        self.call_window = None
        self.pending_upload = False

        self.grid_columnconfigure(2, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self._build_ui()
        self._connect_events()
        self._refresh_contacts()
        self._open_global()
        self._start_workers()

    def _build_ui(self):
        rail = ctk.CTkFrame(self, width=72, corner_radius=0, fg_color="#1e1f22")
        rail.grid(row=0, column=0, sticky="ns")
        rail.grid_propagate(False)
        ctk.CTkButton(
            rail, text="GC", width=48, height=48, corner_radius=16, font=ctk.CTkFont(size=17, weight="bold"),
            command=self._open_global,
        ).pack(padx=12, pady=(14, 8))
        ctk.CTkFrame(rail, height=2, width=36, fg_color="#35363c").pack(pady=4)
        ctk.CTkButton(rail, text="＋", width=48, height=48, corner_radius=24, command=self._new_dm).pack(pady=8)

        sidebar = ctk.CTkFrame(self, width=260, corner_radius=0, fg_color="#2b2d31")
        sidebar.grid(row=0, column=1, sticky="ns")
        sidebar.grid_propagate(False)
        sidebar.grid_rowconfigure(2, weight=1)
        sidebar.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(sidebar, text="DIRECT MESSAGES", anchor="w", text_color="#b5bac1",
                     font=ctk.CTkFont(size=12, weight="bold")).grid(row=0, column=0, padx=16, pady=(18, 6), sticky="ew")
        ctk.CTkButton(sidebar, text="＋ New direct message", anchor="w", fg_color="transparent",
                      hover_color="#35373c", text_color="#dbdee1", command=self._new_dm).grid(
            row=1, column=0, padx=8, pady=(0, 4), sticky="ew"
        )
        self.contacts_frame = ctk.CTkScrollableFrame(sidebar, fg_color="transparent", corner_radius=0)
        self.contacts_frame.grid(row=2, column=0, sticky="nsew", padx=4)
        self.contacts_frame.grid_columnconfigure(0, weight=1)

        me = ctk.CTkFrame(sidebar, height=58, corner_radius=0, fg_color="#232428")
        me.grid(row=3, column=0, sticky="ew")
        me.grid_propagate(False)
        self.me_label = ctk.CTkLabel(me, text=g_username, anchor="w", font=ctk.CTkFont(weight="bold"))
        self.me_label.pack(side="left", padx=12, fill="x", expand=True)
        ctk.CTkButton(me, text="⚙", width=38, fg_color="transparent", hover_color="#3d3f45",
                      command=self._edit_profile).pack(side="right", padx=6)

        main = ctk.CTkFrame(self, corner_radius=0, fg_color="#313338")
        main.grid(row=0, column=2, sticky="nsew")
        main.grid_columnconfigure(0, weight=1)
        main.grid_rowconfigure(1, weight=1)

        header = ctk.CTkFrame(main, height=58, corner_radius=0, fg_color="#313338", border_width=0)
        header.grid(row=0, column=0, sticky="ew")
        header.grid_propagate(False)
        self.title_label = ctk.CTkLabel(header, text="# global", font=ctk.CTkFont(size=17, weight="bold"))
        self.title_label.pack(side="left", padx=18)
        self.presence_label = ctk.CTkLabel(header, text="", text_color="#949ba4")
        self.presence_label.pack(side="left")
        self.call_button = ctk.CTkButton(header, text="☎ Call", width=90, command=self._call_clicked)
        self.call_button.pack(side="right", padx=16, pady=10)
        self.older_button = ctk.CTkButton(header, text="Load older", width=100, fg_color="#4e5058",
                                          hover_color="#5c5e66", command=self._load_older)
        self.older_button.pack(side="right", pady=10)

        self.message_frame = ctk.CTkScrollableFrame(main, fg_color="#313338", corner_radius=0)
        self.message_frame.grid(row=1, column=0, sticky="nsew", padx=4)
        self.message_frame.grid_columnconfigure(0, weight=1)

        composer = ctk.CTkFrame(main, fg_color="#383a40", corner_radius=9, height=52)
        composer.grid(row=2, column=0, padx=16, pady=(8, 18), sticky="ew")
        composer.grid_columnconfigure(1, weight=1)
        ctk.CTkButton(composer, text="＋", width=42, fg_color="transparent", hover_color="#4a4c52",
                      command=self._attach_file).grid(row=0, column=0, padx=(4, 0), pady=5)
        self.message_entry = ctk.CTkEntry(composer, border_width=0, fg_color="transparent",
                                          placeholder_text="Message #global")
        self.message_entry.grid(row=0, column=1, padx=6, pady=5, sticky="ew")
        self.message_entry.bind("<Return>", lambda _event: self._send())
        ctk.CTkButton(composer, text="Send", width=72, command=self._send).grid(row=0, column=2, padx=6, pady=6)

    def _connect_events(self):
        app_signals.new_message.connect(self._on_global_message)
        app_signals.dm_message.connect(self._on_dm_message)
        app_signals.history_batch.connect(self._on_history)
        app_signals.users_updated.connect(self._on_users)
        app_signals.incoming_call.connect(self._incoming_call)
        app_signals.call_status.connect(self._call_status)

    def _start_workers(self):
        for target in (self._poll_global, self._poll_dms, self._poll_users, self._heartbeat, self._poll_webrtc):
            threading.Thread(target=target, daemon=True).start()

    def _set_channel(self, target):
        global g_current_dm
        with g_dm_lock:
            g_current_dm = target
        self.view_token += 1
        self.messages = []
        self.message_ids = set()
        self.oldest_id = None
        for child in self.message_frame.winfo_children():
            child.destroy()
        if target:
            profile = safe_profile(target)
            self.title_label.configure(text=f"@ {profile['display_name']}")
            self.presence_label.configure(text="Online" if target in g_online_users else "Offline")
            self.call_button.configure(state="normal")
            self.message_entry.configure(placeholder_text=f"Message @{profile['display_name']}")
        else:
            self.title_label.configure(text="# global")
            self.presence_label.configure(text="Everyone")
            self.call_button.configure(state="disabled")
            self.message_entry.configure(placeholder_text="Message #global")
        self._load_history()

    def _open_global(self):
        self._set_channel("")

    def _open_dm(self, username):
        if not username or username == g_username:
            return
        safe_profile(username)
        save_contacts()
        self._refresh_contacts()
        self._set_channel(username)

    def _new_dm(self):
        username = simpledialog.askstring("New direct message", "Username:", parent=self)
        if username:
            self._open_dm(username.strip()[:80])

    def _refresh_contacts(self):
        for child in self.contacts_frame.winfo_children():
            child.destroy()
        contacts = sorted(g_contacts, key=lambda name: (name not in g_online_users, safe_profile(name)["display_name"].lower()))
        for username in contacts:
            if username in {g_username, "SYSTEM"}:
                continue
            profile = safe_profile(username)
            row = ctk.CTkFrame(self.contacts_frame, fg_color="transparent", corner_radius=6)
            row.grid(sticky="ew", padx=2, pady=1)
            row.grid_columnconfigure(1, weight=1)
            dot_color = "#23a55a" if username in g_online_users else "#80848e"
            ctk.CTkLabel(row, text="●", width=18, text_color=dot_color).grid(row=0, column=0, padx=(5, 0))
            button = ctk.CTkButton(
                row, text=profile["display_name"], anchor="w", height=40, fg_color="transparent",
                hover_color="#3f4147", text_color="#f2f3f5" if username in g_online_users else "#949ba4",
                command=lambda name=username: self._open_dm(name),
            )
            image = contact_image(profile.get("profile_picture", ""), 30)
            if image:
                button.configure(image=image, compound="left")
                button.image = image
            button.grid(row=0, column=1, sticky="ew")

    def _history_endpoint(self, before=None):
        with g_dm_lock:
            target = g_current_dm
        if target:
            endpoint = f"/dm_messages?user={quote(g_username)}&with={quote(target)}&limit=100"
        else:
            endpoint = "/messages?limit=100"
        if before is not None:
            endpoint += f"&before={before}"
        return endpoint, target

    def _load_history(self, before=None, prepend=False):
        token = self.view_token
        endpoint, target = self._history_endpoint(before)
        threading.Thread(target=self._fetch_history, args=(token, endpoint, target, prepend), daemon=True).start()

    def _load_older(self):
        if self.oldest_id is not None:
            self._load_history(self.oldest_id, True)

    def _fetch_history(self, token, endpoint, target, prepend):
        data = http_get(endpoint)
        if not isinstance(data, list):
            data = []
        messages = [self._normalise_message(item) for item in data]
        app_signals.history_batch.emit(token, messages, prepend, target)

    @staticmethod
    def _normalise_message(item):
        sender = item.get("sender", item.get("username", ""))
        return {
            "id": item.get("id", 0), "sender": sender, "text": item.get("message", ""),
            "is_system": sender == "SYSTEM", "profile": item.get("profile") or {},
            "attachment": item.get("attachment") or {}, "time": item.get("time"),
        }

    def _on_history(self, token, messages, prepend, target):
        with g_dm_lock:
            current = g_current_dm
        if token != self.view_token or target != current:
            return
        fresh = [message for message in messages if message["id"] not in self.message_ids]
        for message in fresh:
            self.message_ids.add(message["id"])
            safe_profile(message["sender"], message.get("profile"))
        self.messages = fresh + self.messages if prepend else self.messages + fresh
        ids = [message["id"] for message in self.messages if message["id"]]
        if ids:
            self.oldest_id = min(ids)
        self._render_messages(scroll_to_bottom=not prepend)

    def _render_messages(self, scroll_to_bottom=True):
        for child in self.message_frame.winfo_children():
            child.destroy()
        previous_sender = None
        for message in self.messages:
            sender = message["sender"]
            compact = sender == previous_sender and not message["is_system"]
            self._message_widget(message, compact)
            previous_sender = sender
        if scroll_to_bottom:
            self.after(40, lambda: self.message_frame._parent_canvas.yview_moveto(1.0))

    def _message_widget(self, message, compact=False):
        if message["is_system"]:
            ctk.CTkLabel(self.message_frame, text=message["text"], anchor="w", text_color="#949ba4").grid(
                sticky="ew", padx=18, pady=4
            )
            return
        profile = safe_profile(message["sender"], message.get("profile"))
        row = ctk.CTkFrame(self.message_frame, fg_color="transparent")
        row.grid(sticky="ew", padx=12, pady=(1 if compact else 7, 1))
        row.grid_columnconfigure(1, weight=1)
        if not compact:
            avatar = contact_image(profile.get("profile_picture", ""), 40)
            avatar_label = ctk.CTkLabel(row, text="", image=avatar, width=44)
            avatar_label.grid(row=0, column=0, rowspan=3, padx=(0, 10), sticky="n")
            avatar_label.image = avatar
            ctk.CTkLabel(row, text=profile["display_name"], anchor="w", text_color=profile["name_color"],
                         font=ctk.CTkFont(size=14, weight="bold")).grid(row=0, column=1, sticky="w")
            text_row = 1
        else:
            ctk.CTkLabel(row, text="", width=44).grid(row=0, column=0, padx=(0, 10))
            text_row = 0
        ctk.CTkLabel(row, text=message["text"] or ("📎 Attachment" if message.get("attachment") else ""),
                     anchor="w", justify="left", wraplength=780, text_color="#dbdee1").grid(
            row=text_row, column=1, sticky="ew"
        )
        attachment = message.get("attachment") or {}
        if attachment.get("url"):
            filename = attachment.get("filename") or "Download attachment"
            url = urljoin(BASE_URL + "/", attachment["url"].lstrip("/"))
            ctk.CTkButton(row, text=f"📎 {filename}", width=220, anchor="w", fg_color="#2b2d31",
                          hover_color="#232428", command=lambda link=url: webbrowser.open(link)).grid(
                row=text_row + 1, column=1, pady=5, sticky="w"
            )

    def _send(self):
        text = self.message_entry.get().strip()
        if not text:
            return
        self.message_entry.delete(0, "end")
        self._send_message(text)

    def _send_message(self, text, attachment_id=None):
        with g_dm_lock:
            target = g_current_dm
        if target:
            payload = {"username": g_username, "password": g_password, "to": target,
                       "message": text, "attachment_id": attachment_id}
            safe_profile(target)
            save_contacts()
            endpoint = "/dm_send"
        else:
            payload = {"username": g_username, "password": g_password, "message": text,
                       "attachment_id": attachment_id}
            endpoint = "/send"
        threading.Thread(target=http_post, args=(endpoint, payload), daemon=True).start()

    def _attach_file(self):
        path = filedialog.askopenfilename(parent=self, title="Choose a file")
        if not path:
            return
        try:
            if os.path.getsize(path) > 15 * 1024 * 1024:
                messagebox.showwarning("File too large", "Choose a file under 15 MB.", parent=self)
                return
        except OSError as exc:
            messagebox.showerror("Upload failed", str(exc), parent=self)
            return
        threading.Thread(target=self._upload_file, args=(path,), daemon=True).start()

    def _upload_file(self, path):
        try:
            with open(path, "rb") as handle:
                encoded = base64.b64encode(handle.read()).decode("ascii")
            result = http_post("/upload", {
                "username": g_username, "password": g_password, "filename": os.path.basename(path),
                "mime_type": mimetypes.guess_type(path)[0] or "application/octet-stream", "data": encoded,
            })
            if isinstance(result, dict) and result.get("attachment"):
                self._send_message("", result["attachment"]["id"])
            else:
                app_signals.call_status.emit((result or {}).get("error", "Upload failed"))
        except Exception as exc:
            app_signals.call_status.emit(f"Upload failed: {exc}")

    def _on_global_message(self, message_id, sender, text, is_system, profile, attachment):
        with g_dm_lock:
            target = g_current_dm
        if target or message_id in self.message_ids:
            return
        message = {"id": message_id, "sender": sender, "text": text, "is_system": is_system,
                   "profile": profile, "attachment": attachment}
        self.message_ids.add(message_id)
        self.messages.append(message)
        self._message_widget(message, self.messages[-2]["sender"] == sender if len(self.messages) > 1 else False)
        self.after(30, lambda: self.message_frame._parent_canvas.yview_moveto(1.0))

    def _on_dm_message(self, contact, message_id, sender, text, profile, attachment):
        safe_profile(contact, profile if sender == contact else None)
        save_contacts()
        self._refresh_contacts()
        if sender != g_username:
            sender_profile = safe_profile(sender, profile)
            desktop_notify(f"Message from {sender_profile['display_name']}", text or "Sent an attachment")
        with g_dm_lock:
            target = g_current_dm
        if target != contact or message_id in self.message_ids:
            return
        message = {"id": message_id, "sender": sender, "text": text, "is_system": False,
                   "profile": profile, "attachment": attachment}
        self.message_ids.add(message_id)
        self.messages.append(message)
        self._message_widget(message, self.messages[-2]["sender"] == sender if len(self.messages) > 1 else False)
        self.after(30, lambda: self.message_frame._parent_canvas.yview_moveto(1.0))

    def _on_users(self, user_list):
        global g_online_users
        online = set()
        for user in user_list:
            username = user if isinstance(user, str) else user.get("username", "")
            if not username or username == g_username:
                continue
            online.add(username)
            safe_profile(username, user if isinstance(user, dict) else None)
        g_online_users = online
        save_contacts()
        self._refresh_contacts()
        with g_dm_lock:
            target = g_current_dm
        if target:
            self.presence_label.configure(text="Online" if target in online else "Offline")

    def _poll_global(self):
        global g_last_id
        initial = http_get("/messages?limit=100")
        if isinstance(initial, list):
            g_last_id = max([item.get("id", -1) for item in initial] or [-1])
        while not self.stop_event.wait(0.8):
            data = http_get(f"/messages?after={g_last_id}")
            if not isinstance(data, list):
                continue
            for item in data:
                mid = item.get("id", 0)
                if mid <= g_last_id:
                    continue
                g_last_id = mid
                sender = item.get("username", "")
                app_signals.new_message.emit(mid, sender, item.get("message", ""), sender == "SYSTEM",
                                             item.get("profile") or {}, item.get("attachment") or {})

    def _poll_dms(self):
        last_id = -1
        ready = False
        while not self.stop_event.wait(1.0):
            suffix = f"&after={last_id}" if ready else "&limit=100"
            data = http_get(f"/dm_messages?user={quote(g_username)}{suffix}")
            if not isinstance(data, list):
                continue
            for item in data:
                mid = item.get("id", 0)
                sender = item.get("sender", item.get("username", ""))
                recipient = item.get("recipient", item.get("to", item.get("target", "")))
                contact = sender if sender and sender != g_username else recipient
                if not contact or contact in {g_username, "SYSTEM"}:
                    continue
                safe_profile(contact, item.get("profile") if sender == contact else None)
                if ready and mid > last_id:
                    app_signals.dm_message.emit(contact, mid, sender, item.get("message", ""),
                                                item.get("profile") or {}, item.get("attachment") or {})
                last_id = max(last_id, mid)
            if not ready:
                ready = True
                save_contacts()

    def _poll_users(self):
        while not self.stop_event.is_set():
            data = http_get("/who")
            if isinstance(data, list):
                app_signals.users_updated.emit(data)
            self.stop_event.wait(2)

    def _heartbeat(self):
        while not self.stop_event.is_set():
            http_post("/heartbeat", {"username": g_username, "password": g_password})
            self.stop_event.wait(12)

    def _poll_webrtc(self):
        while not self.stop_event.wait(1):
            with g_call_lock:
                active, pending = g_call["active"], g_call["pending"]
            if active or pending:
                continue
            data = http_get(f"/webrtc_poll?username={quote(g_username)}")
            if not isinstance(data, dict) or not data.get("offers"):
                continue
            offer = data["offers"][0]
            caller = offer["caller"]
            safe_profile(caller, offer.get("profile"))
            with g_call_lock:
                g_call.update({"pending": True, "pending_caller": caller, "pending_sdp": offer["sdp"],
                               "pending_sid": offer["session_id"], "pending_ice": data.get("ice") or []})
            app_signals.incoming_call.emit(caller)

    def _call_clicked(self):
        with g_dm_lock:
            target = g_current_dm
        if not target:
            return
        with g_call_lock:
            active = g_call["active"]
        if active:
            end_call()
            if self.call_window and self.call_window.winfo_exists():
                self.call_window.destroy()
            self.call_window = None
            return
        self.call_window = CallWindow(self, safe_profile(target)["display_name"])
        threading.Thread(target=start_call_caller, args=(target,), daemon=True).start()

    def _incoming_call(self, caller):
        profile = safe_profile(caller)
        desktop_notify("Incoming Global Chat call", profile["display_name"])
        with g_call_lock:
            sdp, sid = g_call["pending_sdp"], g_call["pending_sid"]
            pending_ice = list(g_call.get("pending_ice", []))
        if messagebox.askyesno("Incoming call", f"{profile['display_name']} is calling. Accept?", parent=self):
            self.call_window = CallWindow(self, profile["display_name"])
            threading.Thread(target=start_call_callee, args=(caller, sdp, sid, pending_ice), daemon=True).start()
        else:
            http_post("/webrtc_reject", {"target": caller, "session_id": sid})
            with g_call_lock:
                g_call["pending"] = False
                g_call["pending_ice"] = []

    def _call_status(self, status):
        if status.startswith("Upload failed"):
            messagebox.showerror("Global Chat", status, parent=self)
        if status in {"Call rejected", "Call ended", "No answer"} and self.call_window:
            self.call_window._set_status(status)

    def _edit_profile(self):
        profile = safe_profile(g_username)
        name = simpledialog.askstring("Display name", "Display name:", initialvalue=profile["display_name"], parent=self)
        if not name:
            return
        color = colorchooser.askcolor(profile["name_color"], parent=self, title="Name color")[1]
        if not color:
            return
        picture = profile.get("profile_picture", "")
        if messagebox.askyesno("Profile picture", "Choose a new profile picture?", parent=self):
            path = filedialog.askopenfilename(parent=self, filetypes=[("Images", "*.png *.jpg *.jpeg *.gif *.webp")])
            if path:
                if os.path.getsize(path) > 450000:
                    messagebox.showwarning("Picture too large", "Choose an image under 450 KB.", parent=self)
                    return
                picture = data_url_from_file(path)
        result = http_post("/profile", {"username": g_username, "password": g_password,
                           "display_name": name.strip()[:40], "name_color": color, "profile_picture": picture})
        if isinstance(result, dict) and result.get("profile"):
            safe_profile(g_username, result["profile"])
            self.me_label.configure(text=result["profile"].get("display_name", g_username))
        elif isinstance(result, dict) and result.get("error"):
            messagebox.showerror("Profile error", result["error"], parent=self)

    def shutdown(self):
        self.stop_event.set()
        save_contacts()
        http_post("/leave", {"username": g_username})
        end_call()


class GlobalChatApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")
        self.title("Global Chat")
        self.geometry("1180x760")
        self.minsize(900, 620)
        self.chat_view = None
        self.protocol("WM_DELETE_WINDOW", self._close)
        app_signals.login_result.connect(self._finish_login)
        self._show_login()
        self.after(25, self._dispatch_events)

    def _clear(self):
        for child in self.winfo_children():
            child.destroy()

    def _show_login(self):
        self._clear()
        card = ctk.CTkFrame(self, width=440, height=410, fg_color="#2b2d31", corner_radius=12)
        card.place(relx=0.5, rely=0.5, anchor="center")
        card.pack_propagate(False)
        ctk.CTkLabel(card, text="Welcome back!", font=ctk.CTkFont(size=27, weight="bold")).pack(pady=(38, 4))
        ctk.CTkLabel(card, text="Log in or create your Global Chat account", text_color="#b5bac1").pack(pady=(0, 24))
        self.user_entry = ctk.CTkEntry(card, width=350, height=44, placeholder_text="Username")
        self.user_entry.pack(pady=7)
        self.password_entry = ctk.CTkEntry(card, width=350, height=44, placeholder_text="Password", show="•")
        self.password_entry.pack(pady=7)
        self.password_entry.bind("<Return>", lambda _event: self._login())
        self.login_button = ctk.CTkButton(card, text="Log In / Register", width=350, height=44, command=self._login)
        self.login_button.pack(pady=(18, 8))
        self.login_status = ctk.CTkLabel(card, text="", text_color="#f23f42")
        self.login_status.pack()
        self.after(100, self.user_entry.focus_set)

    def _login(self):
        username = self.user_entry.get().strip()
        password = self.password_entry.get()
        if not username or not password:
            self.login_status.configure(text="Username and password are required.")
            return
        self.login_button.configure(state="disabled", text="Connecting…")
        threading.Thread(target=self._login_worker, args=(username, password), daemon=True).start()

    @staticmethod
    def _login_worker(username, password):
        result = http_post("/auth", {"username": username, "password": password})
        app_signals.login_result.emit(username, password, result)

    def _finish_login(self, username, password, result):
        global g_username, g_password
        if isinstance(result, dict) and result.get("error"):
            self.login_button.configure(state="normal", text="Log In / Register")
            self.login_status.configure(text=result["error"])
            return
        g_username, g_password = username, password
        load_contacts()
        if isinstance(result, dict) and result.get("profile"):
            safe_profile(username, result["profile"])
        if WEBRTC:
            threading.Thread(target=_webrtc_thread, daemon=True).start()
            time.sleep(0.1)
        self._clear()
        self.chat_view = ChatView(self)
        self.chat_view.pack(fill="both", expand=True)

    def _dispatch_events(self):
        try:
            while True:
                signal, args = UI_EVENTS.get_nowait()
                for callback in list(signal.callbacks):
                    try:
                        callback(*args)
                    except (tk.TclError, RuntimeError):
                        pass
        except queue.Empty:
            pass
        if self.winfo_exists():
            self.after(25, self._dispatch_events)

    def _close(self):
        if self.chat_view:
            self.chat_view.shutdown()
        self.destroy()


def main():
    if IS_WINDOWS:
        try:
            import ctypes

            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("GlobalChat.Client")
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    app = GlobalChatApp()
    app.mainloop()


if __name__ == "__main__":
    main()
