"""Reference outcomes from h2's codecs (hyperframe 6.1.0, hpack 4.2.0, as
pinned by h2 4.4.1) for tests/Conformance.lean, "h2 golden". One line per case,
fields separated by '|', bytes in hex:

  frame|name|wire                      hyperframe serializes `wire`
  badframe|name|wire|exception         hyperframe refuses `wire` (ours refuses it
                                       when parsing, or the connection does)
  hpack|case|table size|huffman|block|fields   one block of a case's sequence;
                                       fields are name=value;… in hex, `!` marks never-indexed
  badhpack|name|max list|block|exception
  huff|input|encoded                   hpack's Huffman encoding of `input`
  badhuff|encoded|exception

Run with the upstream venv:

  upstream-spec/.venv/bin/python -I tests/upstream/h2_golden.py
"""
from hyperframe.frame import (Frame, DataFrame, HeadersFrame, PriorityFrame, RstStreamFrame,
    SettingsFrame, PushPromiseFrame, PingFrame, GoAwayFrame, WindowUpdateFrame,
    ContinuationFrame, ExtensionFrame)
import hpack
from hpack import Encoder, Decoder, NeverIndexedHeaderTuple
from hpack.huffman import HuffmanEncoder
from hpack.huffman_constants import REQUEST_CODES, REQUEST_CODES_LENGTH
from hpack.huffman_table import decode_huffman

def h(b): return bytes(b).hex()

def frame(name, f):
    print(f"frame|{name}|{h(f.serialize())}")

def parse(wire):
    f, length = Frame.parse_frame_header(memoryview(wire[:9]))
    f.parse_body(memoryview(wire[9:9 + length]))
    return f

def badframe(name, wire):
    try:
        parse(wire); print(f"badframe|{name}|{h(wire)}|accepted")
    except Exception as e:
        print(f"badframe|{name}|{h(wire)}|{type(e).__name__}")

def d(sid, data=b"", flags=(), pad=0):
    f = DataFrame(sid, data, flags=flags)
    if pad: f.pad_length = pad
    return f

frame("data", d(1, b"hello"))
frame("data end stream", d(3, b"", ("END_STREAM",)))
frame("data padded", d(1, b"abc", ("PADDED", "END_STREAM"), pad=4))
frame("data padded zero", d(5, b"x", ("PADDED",), pad=0))
frame("data large id", d(2**31 - 1, b"z"))
hf = HeadersFrame(1, b"\x82\x86\x84", flags=("END_HEADERS",)); frame("headers", hf)
hf = HeadersFrame(3, b"\x88", flags=("END_HEADERS", "END_STREAM", "PRIORITY"))
hf.depends_on, hf.stream_weight, hf.exclusive = 1, 15, True; frame("headers priority", hf)
hf = HeadersFrame(5, b"\x88", flags=("PADDED", "PRIORITY"))
hf.pad_length, hf.depends_on, hf.stream_weight, hf.exclusive = 3, 7, 255, False; frame("headers padded priority", hf)
pf = PriorityFrame(3); pf.depends_on, pf.stream_weight, pf.exclusive = 1, 200, True; frame("priority", pf)
frame("rst stream", RstStreamFrame(1, error_code=8))
frame("settings", SettingsFrame(0, settings={2: 0, 3: 100, 6: 65536}))
frame("settings ack", SettingsFrame(0, flags=("ACK",)))
frame("settings empty", SettingsFrame(0))
pp = PushPromiseFrame(1, promised_stream_id=2, data=b"\x82", flags=("END_HEADERS",)); frame("push promise", pp)
frame("ping", PingFrame(0, opaque_data=b"12345678"))
frame("ping ack", PingFrame(0, opaque_data=b"\x00" * 8, flags=("ACK",)))
frame("goaway", GoAwayFrame(0, last_stream_id=7, error_code=1, additional_data=b"bye"))
frame("goaway empty", GoAwayFrame(0, last_stream_id=0, error_code=0))
frame("window update connection", WindowUpdateFrame(0, window_increment=2**24))
frame("window update stream", WindowUpdateFrame(1, window_increment=2**31 - 1))
frame("continuation", ContinuationFrame(1, b"\x84", flags=("END_HEADERS",)))
def hdr(length, typ, flags, sid): return length.to_bytes(3, "big") + bytes([typ, flags]) + sid.to_bytes(4, "big")
# An ExtensionFrame is printed back as parsed: one built with a body prints a
# length of 0 (its body_len is set only by parse_body).
frame("unknown type", parse(hdr(3, 0xfa, 5, 1) + b"ext"))
badframe("ping short", hdr(7, 6, 0, 0) + b"1234567")
badframe("ping on stream", hdr(8, 6, 0, 1) + b"12345678")
badframe("settings odd length", hdr(5, 4, 0, 0) + b"\x00\x03\x00\x00\x00")
badframe("settings on stream", hdr(0, 4, 0, 1))
badframe("data on stream 0", hdr(1, 0, 0, 0) + b"x")
badframe("data padding too long", hdr(3, 0, 8, 1) + b"\x05ab")
badframe("rst stream short", hdr(3, 3, 0, 1) + b"\x00\x00\x08")
badframe("priority long", hdr(6, 2, 0, 1) + b"\x00" * 6)
badframe("window update zero", hdr(4, 8, 0, 1) + b"\x00\x00\x00\x00")
badframe("window update short", hdr(3, 8, 0, 1) + b"\x00\x00\x01")
badframe("headers on stream 0", hdr(1, 1, 4, 0) + b"\x82")
badframe("continuation on stream 0", hdr(1, 9, 4, 0) + b"\x82")
badframe("goaway on stream", hdr(8, 7, 0, 1) + b"\x00" * 8)
badframe("goaway short", hdr(7, 7, 0, 0) + b"\x00" * 7)

def fields(hs):
    return ";".join(("!" if isinstance(t, NeverIndexedHeaderTuple) else "") + h(t[0]) + "=" + h(t[1]) for t in hs)

def hcase(name, blocks, size=4096, huffman=True):
    e = Encoder(); dec = Decoder()
    if size != 4096: e.header_table_size = size
    for hs in blocks:
        b = e.encode(hs, huffman=huffman)
        got = dec.decode(b, raw=True)
        print(f"hpack|{name}|{size}|{int(huffman)}|{h(b)}|{fields(got)}")

c3 = [[(b":method", b"GET"), (b":scheme", b"http"), (b":path", b"/"), (b":authority", b"www.example.com")],
      [(b":method", b"GET"), (b":scheme", b"http"), (b":path", b"/"), (b":authority", b"www.example.com"), (b"cache-control", b"no-cache")],
      [(b":method", b"GET"), (b":scheme", b"https"), (b":path", b"/index.html"), (b":authority", b"www.example.com"), (b"custom-key", b"custom-value")]]
c5 = [[(b":status", b"302"), (b"cache-control", b"private"), (b"date", b"Mon, 21 Oct 2013 20:13:21 GMT"), (b"location", b"https://www.example.com")],
      [(b":status", b"307"), (b"cache-control", b"private"), (b"date", b"Mon, 21 Oct 2013 20:13:21 GMT"), (b"location", b"https://www.example.com")],
      [(b":status", b"200"), (b"cache-control", b"private"), (b"date", b"Mon, 21 Oct 2013 20:13:22 GMT"), (b"location", b"https://www.example.com"),
       (b"content-encoding", b"gzip"), (b"set-cookie", b"foo=ASDJKHQKBZXOQWEOPIUAXQWEOIU; max-age=3600; version=1")]]
hcase("rfc7541 c3 requests", c3, huffman=False)
hcase("rfc7541 c4 requests huffman", c3)
hcase("rfc7541 c5 responses table 256", c5, size=256, huffman=False)
hcase("rfc7541 c6 responses huffman table 256", c5, size=256)
for huff in (False, True):
    sfx = " huffman" if huff else ""
    hcase("sensitive" + sfx, [[(b":method", b"GET"), (b"authorization", b"secret", True), (b"x-a", b"1")],
                              [(b"authorization", b"secret", True), (b"x-a", b"1")]], huffman=huff)
    hcase("eviction table 64" + sfx, [[(b"x-long-name", b"v" * 20), (b"x-b", b"2")], [(b"x-long-name", b"v" * 20), (b"x-b", b"2")]], size=64, huffman=huff)
    hcase("table size 0" + sfx, [[(b"x-a", b"1"), (b"x-a", b"1")]], size=0, huffman=huff)
hcase("utf8 and empty value", [[(b"x-empty", b""), ("x-utf8".encode(), "caf\u00e9".encode()), (b"x-bin", bytes(range(256)))]])
# An httpx request as it goes out on HTTP/2 (httpcore's fields, h2's
# normalisation): Huffman literals longer than raw ones included.
hcase("httpx request", [[(b":method", b"GET"), (b":authority", b"example.com"), (b":scheme", b"http"), (b":path", b"/"),
    (b"accept", b"*/*"), (b"accept-encoding", b"gzip, deflate"), (b"user-agent", b"python-httpx/0.28.1"),
    (b"cookie", b"a=1", True), (b"x-symbols", b"{}<>\\^`|~")],
    [(b":method", b"POST"), (b":authority", b"example.com"), (b":scheme", b"http"), (b":path", b"/submit?q=1"),
    (b"content-length", b"2"), (b"content-type", b"application/json")]])

def badhpack(name, block, maxlist=65536, maxtable=None):
    dec = Decoder(max_header_list_size=maxlist)
    if maxtable is not None: dec.max_allowed_table_size = maxtable
    try:
        dec.decode(block); print(f"badhpack|{name}|{maxlist}|{h(block)}|accepted")
    except Exception as e:
        print(f"badhpack|{name}|{maxlist}|{h(block)}|{type(e).__name__}")

badhpack("index 0", b"\x80")
badhpack("index past the tables", b"\xbe")
badhpack("name index past the tables", b"\x7f\x20\x01a")
badhpack("integer overlong", b"\xff\xff\xff\xff\xff\xff\xff\xff\x7f")
badhpack("integer truncated", b"\xff")
badhpack("string truncated", b"\x40\x05ab")
badhpack("size update above max", b"\x3f\xe2\x1f")
badhpack("header list too large", b"\x40\x01a" + b"\x7f\xff\x01" + b"v" * 400, maxlist=100)
badhpack("huffman eos", b"\x40\x81a\x84\xff\xff\xff\xff")

enc = HuffmanEncoder(REQUEST_CODES, REQUEST_CODES_LENGTH)
for s in [b"www.example.com", b"no-cache", b"custom-key", b"custom-value", b"302", b"private",
          b"Mon, 21 Oct 2013 20:13:21 GMT", b"https://www.example.com", b"", bytes(range(256)), b"\xff\xfe\x00"]:
    print(f"huff|{h(s)}|{h(enc.encode(s))}")
for bad in [b"\xff\xff\xff\xff", b"\x00", b"\xfe\x3f", b"\x1f\xff\xff\xff\xff"]:
    try:
        decode_huffman(bad); print(f"badhuff|{h(bad)}|accepted")
    except Exception as e:
        print(f"badhuff|{h(bad)}|{type(e).__name__}")
