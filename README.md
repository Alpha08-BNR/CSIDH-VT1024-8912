# CSIDH-512 Post-Quantum Encrypted Communication System

An end-to-end encrypted (E2EE) data transmission system leveraging the **CSIDH (Commutative Supersingular Isogeny Diffie-Hellman)** algorithm for post-quantum security, combined with OpenCL GPU/CPU key expansion and **AES-256-GCM** authenticated symmetric encryption.

---

## 📌 Key Features

* **Post-Quantum Security:** Implements CSIDH over a 512-bit prime field $p \approx 2^{512}$ (using 74 small primes) for quantum-resistant key exchange.
* **Enhanced Key Derivation (Vector Expansion):** Expands the CSIDH shared secret into a large state vector ($1,024 - 8,192$ elements) through 32 non-linear transformation rounds.
* **GPU Acceleration:** The client supports **OpenCL GPU** acceleration for fast vector expansion calculations, with an automatic fallback to CPU if no compatible OpenCL device is found.
* **Authenticated Encryption:** Uses **AES-256-GCM** to guarantee both confidentiality and integrity/authenticity of transmitted payloads.
* **Public Key Pinning:** Allows the client to pin and verify the server's public key to prevent Man-in-the-Middle (MitM) attacks.
* **Public Key Validation:** Validates elliptic curve parameters to defend against invalid-curve attacks.

---

## 📐 Architecture & Communication Flow

```
Client                                                  Server
  |                                                       |
  |<------------------ Server Public Key (64B) -----------|
  |                                                       |
  | [Verify Server Key (Pinning / Validation)]            |
  | [Generate Client CSIDH Keypair & Shared Secret]       |
  | [Expand Shared Secret -> OpenCL GPU / CPU Vector]     |
  | [Derive AES-256-GCM Key (SHA-256)]                    |
  | [Encrypt Data Payload]                                |
  |                                                       |
  |--- Header (Client Key + Params + IV + Data Size) ---->|
  |--- Ciphertext --------------------------------------->|
  |--- AES-GCM Auth Tag (16B) --------------------------->|
  |                                                       |
  |                                   [Verify & Decrypt]  |
  |<------------------ Status Byte (1B) ------------------|
```

1. **Handshake Initialization:** The server listens on a TCP port and transmits its 64-byte CSIDH public key immediately upon client connection.
2. **CSIDH Key Exchange:** 
   * The client validates the server's public key.
   * The client generates an ephemeral CSIDH keypair and computes the **Shared Secret**.
3. **Key Derivation (KDF):**
   * The shared secret seeds a vector state of size $N$ ($1024 \le N \le 8192$), expanded across 32 rounds via GPU/CPU.
   * SHA-256 hashes the expanded vector to derive a 256-bit **AES-256** session key.
4. **Encryption & Data Transfer:**
   * The payload is encrypted with AES-256-GCM.
   * The client sends the Header, Ciphertext, and Authentication Tag to the server.
   * The server calculates the matching shared secret, decrypts the payload, and sends back a status code (success/failure).

---

## 🛠 System Requirements

### Prerequisites
* **Operating System:** Linux / POSIX compliant.
* **Compiler:** `g++` (supporting C++11 or later).
* **OpenSSL:** Development libraries (`libssl`, `libcrypto`).
* **OpenCL SDK:** Required for GPU acceleration on the client side (e.g., `nvidia-opencl-dev`, `ocl-icd-opencl-dev`, or Intel OpenCL).

### Installing Dependencies (Ubuntu/Debian)

```bash
sudo apt update
sudo apt install build-essential libssl-dev opencl-headers ocl-icd-opencl-dev
```

---

## ⚙️ Compilation

You can compile both client and server binaries using `g++`:

```bash
# Compile Server (CPU only)
g++ -O3 -std=c++11 server-CSIDH-VT1024-8912.cpp -o csidh_server -lcrypto

# Compile Client (Requires OpenCL)
g++ -O3 -std=c++11 client-CSIDH-VT1024-8912.cpp -o csidh_client -lcrypto -lOpenCL
```

---

## 🚀 Usage Guide

### 1. Running the Server

Syntax:
```bash
./csidh_server <port> [output_file]
```

**Example:**
Listen on port `8888` and write decrypted output to `received_data.bin`:
```bash
./csidh_server 8888 received_data.bin
```
*(If `output_file` is omitted, decrypted data will be printed to `stdout`).*

Upon startup, the server outputs its public key in hex format:
```text
Khoa cong khai server: 1a2b3c4d...
Dang lang nghe cong 8888
```

---

### 2. Running the Client

Syntax:
```bash
./csidh_client <host> <port> [vector_size 1024-8192] [input_file|-] [server_public_key_hex]
```

* `host` & `port`: Server IP address and port number.
* `vector_size`: Key expansion vector size (Default: `4096`, valid range: `1024` - `8192`).
* `input_file`: Path to the file to encrypt and send (use `-` for `stdin`).
* `server_public_key_hex` *(Optional)*: Server's hex public key for Public Key Pinning verification.

**Example 1: Send `secret.txt` with default parameters**
```bash
./csidh_client 127.0.0.1 8888 4096 secret.txt
```

**Example 2: Send file with Public Key Pinning enabled**
```bash
./csidh_client 127.0.0.1 8888 4096 secret.txt 1a2b3c4d...
```

**Example 3: Pipe data directly via stdio**
```bash
echo "Top secret message" | ./csidh_client 127.0.0.1 8888 2048 -
```

---

## 📁 Repository Structure

```text
.
├── client-CSIDH-VT1024-8912.cpp   # Client implementation (CSIDH, OpenCL, AES-GCM)
├── server-CSIDH-VT1024-8912.cpp   # Server implementation (CSIDH, CPU-vector, AES-GCM)
└── README.md                       # Project documentation
```

---

## ⚠️ Disclaimer & Security Notice

* This project is an experimental implementation designed for academic research, post-quantum cryptography testing, and performance benchmarking.
* For production environments, please rely on standardized PQC algorithms (such as NIST PQC standards like ML-KEM / Kyber).