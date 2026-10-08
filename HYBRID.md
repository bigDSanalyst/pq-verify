# Hybrid key agreement (RFC 10024)

`--emit-hybrid-prompt` / `--verify-hybrid`: how pq-verify checks the
composition of a hybrid key agreement. The [README](README.md#hybrid-key-agreement-rfc-10024)
has the short version.

Nothing in production negotiates bare ML-KEM. Every deployment that has turned
post-quantum TLS on runs a **hybrid** group, and `X25519MLKEM768` is what
Chrome, Firefox, OpenSSL, BoringSSL and the large CDNs agree on today.

The ML-KEM half of that handshake is covered by `--acvp` and `--audit-kem`.
The **composition** is not — and the composition is where the bugs are,
because RFC 10024 does not use one order:

| Group | Codepoint | Key share | Shared secret |
|---|---|---|---|
| `X25519MLKEM768` | `0x11EC` | ML-KEM ‖ ECDHE | ML-KEM ‖ ECDHE |
| `SecP256r1MLKEM768` | `0x11EB` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |
| `SecP384r1MLKEM1024` | `0x11ED` | ECDHE ‖ ML-KEM | ECDHE ‖ ML-KEM |

The first row is reversed relative to its own name. The RFC says so itself,
and calls it historical. So an implementation can pass **every ACVP vector
byte-for-byte** and still be wrong, because ACVP never sees the concatenation.

The failure is silent in the worst way: two peers that make the same mistake
interoperate happily with each other and with nobody else, and the peer that
got it right sees only a `decrypt_error` with no indication of which side is
at fault.

```bash
pq-verify --emit-hybrid-prompt list          # the groups this build knows
pq-verify --emit-hybrid-prompt X25519MLKEM768 --prompt-out hybrid.json
pq-verify --verify-hybrid hybrid.json
```

What gets checked, from one handshake's wire bytes:

- every length against the value RFC 10024 pins for that group
- the encapsulation key against the FIPS 203 §7.2 check the RFC makes a
  **MUST** for the server — validated here against NIST's own 20 labelled
  `encapsulationKeyCheck` cases, so it agrees with NIST rather than with itself
- the ECDHE share as an uncompressed point on the curve (RFC 9846 §4.3.8.2)
- the X25519 all-zero shared-secret check, which the RFC also makes a MUST
- when you supply an ephemeral private scalar, the ECDHE shared secret
  **recomputed** and compared byte-for-byte at the offset the group pins
- and, when you supply the client's ephemeral ML-KEM decapsulation key, the
  ciphertext in the server share **decapsulated** and the result compared
  byte-for-byte with the ML-KEM half of the combined secret. Without the key,
  nothing ties the ciphertext to the secret, so that check is `NOT CHECKED`
  and the result is `PARTIAL`, never `VERIFIED`

When a check fails, pq-verify tests the other order explicitly:

```
**FAIL**  clientShare ML-KEM-768 encapsulation key (FIPS 203 §7.2)
          there is no valid encapsulation key at offset 0, but there IS one
          at the offset the other order gives — the components are
          concatenated the wrong way round. RFC 10024 pins
          kem_ek ‖ ecdh_pub for X25519MLKEM768
```

That is a root cause, not a mismatch. The discriminator is sound rather than
heuristic: random bytes pass the FIPS 203 §7.2 check with probability below
2⁻¹⁴⁰, so "a valid encapsulation key is sitting at the other offset" is not a
coincidence.

Private keys are optional and should be ephemeral test keys, never production
ones. A field you cannot supply is reported as `NOT CHECKED` and stays out of the ratio; a check that does not exist for a
group — X25519 has no structural share check, and inventing one would report a
check that did not happen — is reported as `N/A` and does not hold the verdict
at `PARTIAL`.
