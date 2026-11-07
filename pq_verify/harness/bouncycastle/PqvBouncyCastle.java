/*
 * pq-verify's Crucible-protocol harness for Bouncy Castle's ML-KEM and ML-DSA,
 * through its lightweight API (written against bcprov 1.86). Run it with
 * Java's source launcher, naming the jar to audit:
 *
 *     pq-verify --audit-harness \
 *         "java -cp bcprov-jdk18on-1.86.jar PqvBouncyCastle.java" ML-KEM-768
 *
 * pq-verify binds its verdict to this file; the handshake names the Bouncy
 * Castle jar actually loaded, with its sha256.
 *
 * Protocol (pq_verify/harness_audit.py): JSON lines, hex inputs and outputs.
 *   ML_KEM_KeyGen  randomness = d || z, param_set  -> ek, dk (FIPS 203 encodings)
 *   ML_KEM_Encaps  ek, randomness = m              -> c, K
 *   ML_KEM_Decaps  c, dk                           -> K
 *   ML_DSA_KeyGen  seed, param_set                 -> pk, sk (FIPS 204 encodings)
 *   ML_DSA_Sign    sk, message = M', rnd, param_set -> signature
 *   ML_DSA_Verify  pk, message = M', signature, param_set -> valid (01 / 00)
 * An exception is an {"error"} reply: the library refused.
 *
 * What each call reaches in Bouncy Castle:
 *   - Randomness goes in through the APIs users call, via a SecureRandom that
 *     serves exactly the given bytes: MLKEMKeyPairGenerator draws d then z,
 *     MLKEMGenerator draws m, MLDSAKeyPairGenerator draws the seed, and the
 *     signers draw rnd. Drawing more or fewer bytes than given is an error.
 *   - Keys are read with the parameter classes' own constructors, which apply
 *     Bouncy Castle's checks (FIPS 203's modulus and hash checks, lengths).
 *   - ML-DSA's M' is signed and verified through the entry point that can
 *     express it, each computing exactly Sign_internal(sk, M', rnd) or
 *     Verify_internal(pk, M', sig):
 *       0 || |ctx| || ctx || M         MLDSASigner with that context (pure)
 *       1 || |ctx| || ctx || OID || PH HashMLDSASigner, when the OID is SHA2-512's
 *                                      (the only pre-hash it implements) and PH
 *                                      is 64 bytes
 *       anything else                  MLDSAEngine's internal functions
 *     rnd = 0^32 is passed as no SecureRandom, Bouncy Castle's deterministic
 *     variant; any other rnd through ParametersWithRandom.
 *   - ML_DSA_Sign takes sk only as FIPS 204's encoding of the parameter set's
 *     private key. Bouncy Castle also reads a 32-byte seed as a private key,
 *     which the protocol's sk is not.
 */
import java.io.FileDescriptor;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.SecureRandom;
import java.security.SecureRandomSpi;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.jar.JarFile;

import org.bouncycastle.crypto.AsymmetricCipherKeyPair;
import org.bouncycastle.crypto.CipherParameters;
import org.bouncycastle.crypto.SecretWithEncapsulation;
import org.bouncycastle.crypto.digests.SHAKEDigest;
import org.bouncycastle.crypto.generators.MLDSAKeyPairGenerator;
import org.bouncycastle.crypto.generators.MLKEMKeyPairGenerator;
import org.bouncycastle.crypto.kems.MLKEMExtractor;
import org.bouncycastle.crypto.kems.MLKEMGenerator;
import org.bouncycastle.crypto.params.MLDSAKeyGenerationParameters;
import org.bouncycastle.crypto.params.MLDSAParameters;
import org.bouncycastle.crypto.params.MLDSAPrivateKeyParameters;
import org.bouncycastle.crypto.params.MLDSAPublicKeyParameters;
import org.bouncycastle.crypto.params.MLKEMKeyGenerationParameters;
import org.bouncycastle.crypto.params.MLKEMParameters;
import org.bouncycastle.crypto.params.MLKEMPrivateKeyParameters;
import org.bouncycastle.crypto.params.MLKEMPublicKeyParameters;
import org.bouncycastle.crypto.params.ParametersWithContext;
import org.bouncycastle.crypto.params.ParametersWithRandom;
import org.bouncycastle.crypto.signers.HashMLDSASigner;
import org.bouncycastle.crypto.signers.MLDSASigner;
import org.bouncycastle.crypto.signers.mldsa.MLDSAEngine;

public final class PqvBouncyCastle {

    private static final String[] FUNCTIONS = {
        "ML_KEM_KeyGen", "ML_KEM_Encaps", "ML_KEM_Decaps",
        "ML_DSA_KeyGen", "ML_DSA_Sign", "ML_DSA_Verify"};

    // DER encoding of id-sha512, 2.16.840.1.101.3.4.2.3, as HashML-DSA's M' carries it
    private static final byte[] SHA2_512_OID = {
        0x06, 0x09, 0x60, (byte) 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03};

    public static void main(String[] args) throws Exception {
        PrintStream out = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
        out.println("{\"implementation\":" + str(implementation())
                    + ",\"functions\":[\"" + String.join("\",\"", FUNCTIONS) + "\"]}");
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
        for (String line; (line = in.readLine()) != null; ) {
            if (!line.trim().isEmpty()) {
                out.println(answer(line));
            }
        }
    }

    /** "Bouncy Castle bcprov 1.86 (<jar>, sha256 <hex>), ...": the jar the
     *  ML-DSA signer class was loaded from, as its manifest names it. */
    static String implementation() throws Exception {
        String path = MLDSASigner.class.getProtectionDomain().getCodeSource().getLocation().toURI().getPath();
        String bundle = "bcprov", version = "unknown version";
        try (JarFile jar = new JarFile(path)) {
            java.util.jar.Attributes a = jar.getManifest().getMainAttributes();
            if (a.getValue("Bundle-Name") != null) {
                bundle = a.getValue("Bundle-Name");
            }
            if (a.getValue("Bundle-Version") != null) {
                version = a.getValue("Bundle-Version");
            }
        }
        MessageDigest sha = MessageDigest.getInstance("SHA-256");
        try (InputStream f = new java.io.FileInputStream(path)) {
            byte[] buf = new byte[1 << 16];
            for (int n; (n = f.read(buf)) > 0; ) {
                sha.update(buf, 0, n);
            }
        }
        String name = path.substring(path.lastIndexOf('/') + 1);
        return "Bouncy Castle " + bundle + " " + version + " (" + name + ", sha256 "
               + hex(sha.digest()) + "), pq-verify's harness";
    }

    static String answer(String line) {
        Map<String, Object> req;
        try {
            req = Json.object(line);
        } catch (RuntimeException e) {
            return error("malformed request: " + e.getMessage());
        }
        String fn = String.valueOf(req.get("function"));
        Map<String, Object> in = Json.map(req.get("inputs"));
        Map<String, Object> params = Json.map(req.get("params"));
        try {
            switch (fn) {
                case "ML_KEM_KeyGen": return kemKeyGen(in, params);
                case "ML_KEM_Encaps": return kemEncaps(in, params);
                case "ML_KEM_Decaps": return kemDecaps(in, params);
                case "ML_DSA_KeyGen": return dsaKeyGen(in, params);
                case "ML_DSA_Sign":   return dsaSign(in, params);
                case "ML_DSA_Verify": return dsaVerify(in, params);
                default:              return "{\"unsupported\":true}";
            }
        } catch (Exception e) {
            return error(e.getClass().getSimpleName() + ": " + e.getMessage());
        }
    }

    // ---- ML-KEM (FIPS 203) ------------------------------------------------

    static MLKEMParameters kemSet(int n) {
        switch (n) {
            case 512:  return MLKEMParameters.ml_kem_512;
            case 768:  return MLKEMParameters.ml_kem_768;
            case 1024: return MLKEMParameters.ml_kem_1024;
            default:   throw new IllegalArgumentException("no ML-KEM-" + n);
        }
    }

    /** The parameter set named in params, or else the one whose key has this length. */
    static MLKEMParameters kemSet(Map<String, Object> params, int len, int[] lens) {
        if (params.containsKey("param_set")) {
            return kemSet(Json.integer(params.get("param_set")));
        }
        int[] sets = {512, 768, 1024};
        for (int i = 0; i < 3; i++) {
            if (lens[i] == len) {
                return kemSet(sets[i]);
            }
        }
        throw new IllegalArgumentException("no ML-KEM parameter set has a " + len + "-byte key");
    }

    static String kemKeyGen(Map<String, Object> in, Map<String, Object> params) {
        MLKEMParameters p = kemSet(Json.integer(params.get("param_set")));
        FixedRandom r = new FixedRandom(bytes(in, "randomness"));
        MLKEMKeyPairGenerator g = new MLKEMKeyPairGenerator();
        g.init(new MLKEMKeyGenerationParameters(r, p));
        AsymmetricCipherKeyPair kp = g.generateKeyPair();
        r.drained("key generation");
        return outputs("ek", ((MLKEMPublicKeyParameters) kp.getPublic()).getEncoded(),
                       "dk", ((MLKEMPrivateKeyParameters) kp.getPrivate()).getEncoded());
    }

    static String kemEncaps(Map<String, Object> in, Map<String, Object> params) {
        byte[] ek = bytes(in, "ek");
        MLKEMParameters p = kemSet(params, ek.length, new int[] {800, 1184, 1568});
        MLKEMPublicKeyParameters pub = new MLKEMPublicKeyParameters(p, ek);
        FixedRandom r = new FixedRandom(bytes(in, "randomness"));
        SecretWithEncapsulation s = new MLKEMGenerator(r).generateEncapsulated(pub);
        r.drained("encapsulation");
        return outputs("c", s.getEncapsulation(), "K", s.getSecret());
    }

    static String kemDecaps(Map<String, Object> in, Map<String, Object> params) {
        byte[] dk = bytes(in, "dk");
        byte[] c = bytes(in, "c");
        MLKEMParameters p = kemSet(params, dk.length, new int[] {1632, 2400, 3168});
        MLKEMPrivateKeyParameters priv = new MLKEMPrivateKeyParameters(p, dk);
        return outputs("K", new MLKEMExtractor(priv).extractSecret(c));
    }

    // ---- ML-DSA (FIPS 204) ------------------------------------------------

    static MLDSAParameters dsaSet(Map<String, Object> params) {
        int n = Json.integer(params.get("param_set"));
        switch (n) {
            case 44: return MLDSAParameters.ml_dsa_44;
            case 65: return MLDSAParameters.ml_dsa_65;
            case 87: return MLDSAParameters.ml_dsa_87;
            default: throw new IllegalArgumentException("no ML-DSA-" + n);
        }
    }

    /** FIPS 204 Table 2: the private key's length. */
    static int skBytes(MLDSAParameters p) {
        if (p == MLDSAParameters.ml_dsa_44) return 2560;
        if (p == MLDSAParameters.ml_dsa_65) return 4032;
        return 4896;
    }

    static String dsaKeyGen(Map<String, Object> in, Map<String, Object> params) {
        MLDSAParameters p = dsaSet(params);
        FixedRandom r = new FixedRandom(bytes(in, "seed"));
        MLDSAKeyPairGenerator g = new MLDSAKeyPairGenerator();
        g.init(new MLDSAKeyGenerationParameters(r, p));
        AsymmetricCipherKeyPair kp = g.generateKeyPair();
        r.drained("key generation");
        return outputs("pk", ((MLDSAPublicKeyParameters) kp.getPublic()).getEncoded(),
                       "sk", ((MLDSAPrivateKeyParameters) kp.getPrivate()).getEncoded());
    }

    /** M' split by FIPS 204's domain separator, when it is one Bouncy Castle's
     *  external API can take: kind 0 pure (rest = M), kind 1 HashML-DSA with
     *  SHA2-512 (rest = PH). Null otherwise. */
    static final class Split {
        final int kind; final byte[] ctx; final byte[] rest;
        Split(int kind, byte[] ctx, byte[] rest) { this.kind = kind; this.ctx = ctx; this.rest = rest; }
    }

    static Split split(byte[] m) {
        if (m.length < 2 || (m[0] != 0 && m[0] != 1)) {
            return null;
        }
        int n = m[1] & 0xff;
        if (2 + n > m.length) {
            return null;
        }
        byte[] ctx = Arrays.copyOfRange(m, 2, 2 + n);
        byte[] rest = Arrays.copyOfRange(m, 2 + n, m.length);
        if (m[0] == 0) {
            return new Split(0, ctx, rest);
        }
        if (rest.length == SHA2_512_OID.length + 64
                && Arrays.equals(Arrays.copyOf(rest, SHA2_512_OID.length), SHA2_512_OID)) {
            return new Split(1, ctx, Arrays.copyOfRange(rest, SHA2_512_OID.length, rest.length));
        }
        return null;
    }

    static String dsaSign(Map<String, Object> in, Map<String, Object> params) throws Exception {
        MLDSAParameters p = dsaSet(params);
        byte[] sk = bytes(in, "sk");
        byte[] m = bytes(in, "message");
        byte[] rnd = bytes(in, "rnd");
        if (sk.length != skBytes(p)) {
            throw new IllegalArgumentException("not a FIPS 204 private key for this set ("
                                               + sk.length + " bytes)");
        }
        if (rnd.length != 32) {
            throw new IllegalArgumentException("rnd is " + rnd.length + " bytes, not 32");
        }
        MLDSAPrivateKeyParameters priv = new MLDSAPrivateKeyParameters(p, sk);
        FixedRandom r = Arrays.equals(rnd, new byte[32]) ? null : new FixedRandom(rnd);
        CipherParameters key = r == null ? priv : new ParametersWithRandom(priv, r);
        Split s = split(m);
        byte[] sig;
        if (s != null && s.kind == 0) {
            MLDSASigner g = new MLDSASigner();
            g.init(true, new ParametersWithContext(key, s.ctx));
            g.update(s.rest, 0, s.rest.length);
            sig = g.generateSignature();
        } else if (s != null) {
            HashMLDSASigner g = new HashMLDSASigner();
            g.init(true, new ParametersWithContext(key, s.ctx));
            sig = g.generateSignature(s.rest);
        } else {
            MLDSAEngine e = MLDSAEngine.getInstance(p, null);
            e.initSign(priv.getTr(), false, null);
            sig = e.signInternal(m, m.length, priv.getRho(), priv.getK(), priv.getT0(),
                                 priv.getS1(), priv.getS2(), rnd);
            r = null;                       // rnd went in as an argument
        }
        if (r != null) {
            r.drained("signing");
        }
        return outputs("signature", sig);
    }

    static String dsaVerify(Map<String, Object> in, Map<String, Object> params) {
        MLDSAParameters p = dsaSet(params);
        byte[] pk = bytes(in, "pk");
        byte[] m = bytes(in, "message");
        byte[] sig = in.containsKey("signature") ? bytes(in, "signature") : bytes(in, "sigma");
        MLDSAPublicKeyParameters pub = new MLDSAPublicKeyParameters(p, pk);
        Split s = split(m);
        boolean ok;
        if (s != null && s.kind == 0) {
            MLDSASigner v = new MLDSASigner();
            v.init(false, new ParametersWithContext(pub, s.ctx));
            v.update(s.rest, 0, s.rest.length);
            ok = v.verifySignature(sig);
        } else if (s != null) {
            HashMLDSASigner v = new HashMLDSASigner();
            v.init(false, new ParametersWithContext(pub, s.ctx));
            ok = v.verifySignature(s.rest, sig);
        } else {
            MLDSAEngine e = MLDSAEngine.getInstance(p, null);
            e.initVerify(pub.getRho(), pub.getT1(), false, null);
            SHAKEDigest d = e.getShake256Digest();
            d.update(m, 0, m.length);
            ok = e.verifyInternal(sig, sig.length, d, pub.getRho(), pub.getT1());
        }
        return outputs("valid", new byte[] {(byte) (ok ? 1 : 0)});
    }

    // ---- randomness ---------------------------------------------------------

    /** Serves exactly the bytes it was given, in order. */
    @SuppressWarnings("serial")
    static final class FixedRandom extends SecureRandom {
        private final byte[] data;
        private int pos;

        FixedRandom(byte[] data) {
            super(new NoSpi(), null);
            this.data = data.clone();
        }

        @Override
        public synchronized void nextBytes(byte[] out) {
            if (pos + out.length > data.length) {
                throw new IllegalStateException("drew " + (pos + out.length)
                                                + " random bytes; " + data.length + " were given");
            }
            System.arraycopy(data, pos, out, 0, out.length);
            pos += out.length;
        }

        @Override
        public byte[] generateSeed(int n) {
            throw new IllegalStateException("asked for a seed outside the given bytes");
        }

        @Override
        public void setSeed(long seed) {
        }

        @Override
        public void setSeed(byte[] seed) {
        }

        void drained(String what) {
            if (pos != data.length) {
                throw new IllegalStateException(what + " drew " + pos + " random bytes; "
                                                + data.length + " were given");
            }
        }
    }

    @SuppressWarnings("serial")
    static final class NoSpi extends SecureRandomSpi {
        @Override protected void engineSetSeed(byte[] seed) { }
        @Override protected void engineNextBytes(byte[] bytes) {
            throw new IllegalStateException("drew randomness outside the given bytes");
        }
        @Override protected byte[] engineGenerateSeed(int n) {
            throw new IllegalStateException("asked for a seed outside the given bytes");
        }
    }

    // ---- JSON lines ---------------------------------------------------------

    static byte[] bytes(Map<String, Object> in, String key) {
        Object v = in.get(key);
        if (!(v instanceof String)) {
            throw new IllegalArgumentException("missing input: " + key);
        }
        String s = (String) v;
        if (s.length() % 2 != 0) {
            throw new IllegalArgumentException("odd-length hex in " + key);
        }
        byte[] b = new byte[s.length() / 2];
        for (int i = 0; i < b.length; i++) {
            int hi = Character.digit(s.charAt(2 * i), 16), lo = Character.digit(s.charAt(2 * i + 1), 16);
            if (hi < 0 || lo < 0) {
                throw new IllegalArgumentException("not hex in " + key);
            }
            b[i] = (byte) ((hi << 4) | lo);
        }
        return b;
    }

    static String hex(byte[] b) {
        StringBuilder sb = new StringBuilder(2 * b.length);
        for (byte x : b) {
            sb.append(Character.forDigit((x >> 4) & 0xf, 16)).append(Character.forDigit(x & 0xf, 16));
        }
        return sb.toString();
    }

    static String outputs(Object... kv) {
        StringBuilder sb = new StringBuilder("{\"outputs\":{");
        for (int i = 0; i < kv.length; i += 2) {
            if (i > 0) {
                sb.append(',');
            }
            sb.append(str((String) kv[i])).append(':').append(str(hex((byte[]) kv[i + 1])));
        }
        return sb.append("}}").toString();
    }

    static String error(String msg) {
        return "{\"error\":" + str(msg == null ? "null" : msg) + "}";
    }

    static String str(String s) {
        StringBuilder sb = new StringBuilder("\"");
        for (char c : s.toCharArray()) {
            if (c == '"' || c == '\\') {
                sb.append('\\').append(c);
            } else if (c < 0x20) {
                sb.append(String.format("\\u%04x", (int) c));
            } else {
                sb.append(c);
            }
        }
        return sb.append('"').toString();
    }

    /** Enough JSON for the requests: objects, strings, numbers, true/false/null. */
    static final class Json {
        private final String s;
        private int i;

        private Json(String s) { this.s = s; }

        @SuppressWarnings("unchecked")
        static Map<String, Object> object(String text) {
            Json j = new Json(text);
            Object v = j.value();
            j.ws();
            if (j.i != text.length() || !(v instanceof Map)) {
                throw new IllegalArgumentException("not one JSON object");
            }
            return (Map<String, Object>) v;
        }

        @SuppressWarnings("unchecked")
        static Map<String, Object> map(Object v) {
            return v instanceof Map ? (Map<String, Object>) v : new LinkedHashMap<>();
        }

        static int integer(Object v) {
            if (v instanceof Number) {
                return ((Number) v).intValue();
            }
            if (v instanceof String) {
                return Integer.parseInt((String) v);
            }
            throw new IllegalArgumentException("missing param_set");
        }

        private void ws() {
            while (i < s.length() && Character.isWhitespace(s.charAt(i))) {
                i++;
            }
        }

        private char next() {
            if (i >= s.length()) {
                throw new IllegalArgumentException("unexpected end");
            }
            return s.charAt(i++);
        }

        private Object value() {
            ws();
            if (i >= s.length()) {
                throw new IllegalArgumentException("unexpected end");
            }
            char c = s.charAt(i);
            if (c == '{') {
                i++;
                Map<String, Object> m = new LinkedHashMap<>();
                ws();
                if (i < s.length() && s.charAt(i) == '}') {
                    i++;
                    return m;
                }
                while (true) {
                    ws();
                    if (next() != '"') {
                        throw new IllegalArgumentException("expected a key");
                    }
                    String k = string();
                    ws();
                    if (next() != ':') {
                        throw new IllegalArgumentException("expected ':'");
                    }
                    m.put(k, value());
                    ws();
                    char d = next();
                    if (d == '}') {
                        return m;
                    }
                    if (d != ',') {
                        throw new IllegalArgumentException("expected ',' or '}'");
                    }
                }
            }
            if (c == '[') {
                i++;
                List<Object> a = new ArrayList<>();
                ws();
                if (i < s.length() && s.charAt(i) == ']') {
                    i++;
                    return a;
                }
                while (true) {
                    a.add(value());
                    ws();
                    char d = next();
                    if (d == ']') {
                        return a;
                    }
                    if (d != ',') {
                        throw new IllegalArgumentException("expected ',' or ']'");
                    }
                }
            }
            if (c == '"') {
                i++;
                return string();
            }
            for (String lit : new String[] {"true", "false", "null"}) {
                if (s.startsWith(lit, i)) {
                    i += lit.length();
                    return lit.equals("null") ? null : Boolean.valueOf(lit.equals("true"));
                }
            }
            int start = i;
            while (i < s.length() && "+-0123456789.eE".indexOf(s.charAt(i)) >= 0) {
                i++;
            }
            if (start == i) {
                throw new IllegalArgumentException("unexpected character");
            }
            String num = s.substring(start, i);
            return num.matches("-?\\d+") ? (Object) Long.valueOf(num) : (Object) Double.valueOf(num);
        }

        /** The rest of a string whose opening quote was read. */
        private String string() {
            StringBuilder sb = new StringBuilder();
            while (true) {
                char c = next();
                if (c == '"') {
                    return sb.toString();
                }
                if (c != '\\') {
                    sb.append(c);
                    continue;
                }
                char e = next();
                switch (e) {
                    case '"': case '\\': case '/': sb.append(e); break;
                    case 'b': sb.append('\b'); break;
                    case 'f': sb.append('\f'); break;
                    case 'n': sb.append('\n'); break;
                    case 'r': sb.append('\r'); break;
                    case 't': sb.append('\t'); break;
                    case 'u':
                        if (i + 4 > s.length()) {
                            throw new IllegalArgumentException("short \\u escape");
                        }
                        sb.append((char) Integer.parseInt(s.substring(i, i + 4), 16));
                        i += 4;
                        break;
                    default: throw new IllegalArgumentException("bad escape");
                }
            }
        }
    }
}
