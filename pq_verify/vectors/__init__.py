"""Pinned NIST ACVP vectors.

This is a package rather than a bare data directory so setuptools cannot
silently omit it: a wheel that builds without these files would install
cleanly and then fail every offline verification at runtime.

See PROVENANCE.md for the upstream commits and MANIFEST.json for per-file
sha256 digests.
"""
