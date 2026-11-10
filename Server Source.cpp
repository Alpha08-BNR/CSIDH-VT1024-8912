#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <openssl/evp.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/types.h>
#include <unistd.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;
typedef unsigned __int128 u128;

struct Fp { u64 v[8]; };
struct Pt { Fp X, Z; };

static const int NPR = 74;
static const u32 ROUNDS = 32;
static int PR[NPR];
static u64 PM[8];
static u64 NPRIME;
static Fp FZERO, FONE, FR2, FINV4, FTWO;
static u64 EXP_INV[8], EXP_LEG[8];

static void mul_small(u64* array_pointer, u64 multiplier) {
    u64 carry = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)array_pointer[i] * multiplier + carry;
        array_pointer[i] = (u64)temporary;
        carry = (u64)(temporary >> 64);
    }
}

static bool ge_p(const u64* array_pointer) {
    for (int i = 7; i >= 0; i--) {
        if (array_pointer[i] > PM[i]) return true;
        if (array_pointer[i] < PM[i]) return false;
    }
    return true;
}

static void sub_p(u64* array_pointer) {
    u64 borrow = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)array_pointer[i] - PM[i] - borrow;
        array_pointer[i] = (u64)temporary;
        borrow = (u64)((temporary >> 64) & 1);
    }
}

static void fadd(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u128 carry = 0;
    for (int i = 0; i < 8; i++) {
        carry += (u128)operand_a.v[i] + operand_b.v[i];
        result.v[i] = (u64)carry;
        carry >>= 64;
    }
    if (carry || ge_p(result.v)) sub_p(result.v);
}

static void fsub(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u64 borrow = 0;
    for (int i = 0; i < 8; i++) {
        u128 temporary = (u128)operand_a.v[i] - operand_b.v[i] - borrow;
        result.v[i] = (u64)temporary;
        borrow = (u64)((temporary >> 64) & 1);
    }
    if (borrow) {
        u128 carry = 0;
        for (int i = 0; i < 8; i++) {
            carry += (u128)result.v[i] + PM[i];
            result.v[i] = (u64)carry;
            carry >>= 64;
        }
    }
}

static void fmul(Fp& result, const Fp& operand_a, const Fp& operand_b) {
    u64 temp_array[10] = {0};
    for (int i = 0; i < 8; i++) {
        u128 carry = 0;
        for (int j = 0; j < 8; j++) {
            carry += (u128)operand_a.v[j] * operand_b.v[i] + temp_array[j];
            temp_array[j] = (u64)carry;
            carry >>= 64;
        }
        carry += temp_array[8];
        temp_array[8] = (u64)carry;
        temp_array[9] = (u64)(carry >> 64);
        u64 multiplier_value = temp_array[0] * NPRIME;
        carry = (u128)multiplier_value * PM[0] + temp_array[0];
        carry >>= 64;
        for (int j = 1; j < 8; j++) {
            carry += (u128)multiplier_value * PM[j] + temp_array[j];
            temp_array[j - 1] = (u64)carry;
            carry >>= 64;
        }
        carry += temp_array[8];
        temp_array[7] = (u64)carry;
        carry >>= 64;
        temp_array[8] = temp_array[9] + (u64)carry;
    }
    for (int i = 0; i < 8; i++) result.v[i] = temp_array[i];
    if (temp_array[8] || ge_p(result.v)) sub_p(result.v);
}

static void fsqr(Fp& result, const Fp& operand_a) { fmul(result, operand_a, operand_a); }

static bool fiszero(const Fp& operand_a) {
    u64 output_mask = 0;
    for (int i = 0; i < 8; i++) output_mask |= operand_a.v[i];
    return output_mask == 0;
}

static bool feq(const Fp& operand_a, const Fp& operand_b) {
    u64 output_mask = 0;
    for (int i = 0; i < 8; i++) output_mask |= operand_a.v[i] ^ operand_b.v[i];
    return output_mask == 0;
}

static void fpow(Fp& result, const Fp& operand_a, const u64* exponent) {
    Fp result_val = FONE;
    for (int i = 511; i >= 0; i--) {
        fsqr(result_val, result_val);
        if ((exponent[i >> 6] >> (i & 63)) & 1) fmul(result_val, result_val, operand_a);
    }
    result = result_val;
}

static void fpow_small(Fp& result, const Fp& operand_a, u64 exponent_val) {
    int top_bit = 63;
    while (top_bit > 0 && !((exponent_val >> top_bit) & 1)) top_bit--;
    Fp result_val = FONE;
    for (int i = top_bit; i >= 0; i--) {
        fsqr(result_val, result_val);
        if ((exponent_val >> i) & 1) fmul(result_val, result_val, operand_a);
    }
    result = result_val;
}

static void finv(Fp& result, const Fp& operand_a) { fpow(result, operand_a, EXP_INV); }

static int fleg(const Fp& operand_a) {
    if (fiszero(operand_a)) return 0;
    Fp result;
    fpow(result, operand_a, EXP_LEG);
    return feq(result, FONE) ? 1 : -1;
}

static Fp tomont(const Fp& operand_a) {
    Fp result;
    fmul(result, operand_a, FR2);
    return result;
}

static Fp frommont(const Fp& operand_a) {
    Fp one, result;
    memset(&one, 0, sizeof one);
    one.v[0] = 1;
    fmul(result, operand_a, one);
    return result;
}

static void init_params() {
    int count = 0;
    for (int prime_candidate = 3; prime_candidate <= 373; prime_candidate += 2) {
        bool is_prime = true;
        for (int divisor = 3; divisor * divisor <= prime_candidate; divisor += 2)
            if (prime_candidate % divisor == 0) { is_prime = false; break; }
        if (is_prime) PR[count++] = prime_candidate;
    }
    PR[count++] = 587;
    memset(PM, 0, sizeof PM);
    PM[0] = 4;
    for (int i = 0; i < NPR; i++) mul_small(PM, (u64)PR[i]);
    PM[0] -= 1;
    u64 inverse = 1;
    for (int i = 0; i < 7; i++) inverse *= 2 - PM[0] * inverse;
    NPRIME = (u64)0 - inverse;
    Fp x_coord;
    memset(&x_coord, 0, sizeof x_coord);
    x_coord.v[0] = 1;
    for (int i = 0; i < 1024; i++) {
        fadd(x_coord, x_coord, x_coord);
        if (i == 511) FONE = x_coord;
    }
    FR2 = x_coord;
    memset(&FZERO, 0, sizeof FZERO);
    fadd(FTWO, FONE, FONE);
    memcpy(EXP_INV, PM, sizeof PM);
    EXP_INV[0] -= 2;
    for (int i = 0; i < 8; i++) EXP_LEG[i] = (PM[i] >> 1) | (i < 7 ? PM[i + 1] << 63 : 0);
    Fp four;
    fadd(four, FTWO, FTWO);
    finv(FINV4, four);
}

static void rnd_bytes(u8* byte_array, size_t length) {
    static FILE* file_pointer = nullptr;
    if (!file_pointer) {
        file_pointer = fopen("/dev/urandom", "rb");
        if (!file_pointer) { fprintf(stderr, "Khong mo duoc /dev/urandom\n"); exit(1); }
    }
    if (fread(byte_array, 1, length, file_pointer) != length) { fprintf(stderr, "Loi doc /dev/urandom\n"); exit(1); }
}

static Fp rnd_fp() {
    Fp result;
    for (;;) {
        rnd_bytes((u8*)result.v, 64);
        result.v[7] &= 0x7FFFFFFFFFFFFFFFULL;
        if (!ge_p(result.v)) return tomont(result);
    }
}

static void rnd_priv(int8_t* priv_array) {
    for (int i = 0; i < NPR; i++) {
        u8 byte_val;
        do rnd_bytes(&byte_val, 1); while (byte_val >= 253);
        priv_array[i] = (int8_t)((int)(byte_val % 11) - 5);
    }
}

static bool pt_inf(const Pt& point_p) { return fiszero(point_p.Z); }

static Fp a24_of(const Fp& curve_a) {
    Fp temp, result;
    fadd(temp, curve_a, FTWO);
    fmul(result, temp, FINV4);
    return result;
}

static void xdbl(Pt& result, const Pt& point_p, const Fp& curve_a24) {
    Fp temp_zero, temp_one, temp_two, temp_three;
    fadd(temp_zero, point_p.X, point_p.Z);
    fsqr(temp_zero, temp_zero);
    fsub(temp_one, point_p.X, point_p.Z);
    fsqr(temp_one, temp_one);
    fsub(temp_two, temp_zero, temp_one);
    fmul(temp_three, curve_a24, temp_two);
    fadd(temp_three, temp_three, temp_one);
    fmul(result.X, temp_zero, temp_one);
    fmul(result.Z, temp_two, temp_three);
}

static void xadd(Pt& result, const Pt& point_p, const Pt& point_q, const Pt& point_d) {
    Fp temp_zero, temp_one, temp_two, temp_three, variable_u, variable_v;
    fsub(temp_zero, point_q.X, point_q.Z);
    fadd(temp_one, point_p.X, point_p.Z);
    fmul(temp_zero, temp_zero, temp_one);
    fadd(temp_two, point_q.X, point_q.Z);
    fsub(temp_three, point_p.X, point_p.Z);
    fmul(temp_one, temp_two, temp_three);
    fadd(variable_u, temp_zero, temp_one);
    fsqr(variable_u, variable_u);
    fsub(variable_v, temp_zero, temp_one);
    fsqr(variable_v, variable_v);
    Pt point_other;
    fmul(point_other.X, point_d.Z, variable_u);
    fmul(point_other.Z, point_d.X, variable_v);
    result = point_other;
}

static void xmul(Pt& result, const Pt& point_p, const u64* scalar_key, const Fp& curve_a24) {
    Pt point_r0, point_r1 = point_p;
    point_r0.X = FONE;
    point_r0.Z = FZERO;
    int top_bit = -1;
    for (int i = 511; i >= 0; i--)
        if ((scalar_key[i >> 6] >> (i & 63)) & 1) { top_bit = i; break; }
    if (top_bit < 0) { result = point_r0; return; }
    for (int i = top_bit; i >= 0; i--) {
        if ((scalar_key[i >> 6] >> (i & 63)) & 1) {
            xadd(point_r0, point_r0, point_r1, point_p);
            xdbl(point_r1, point_r1, curve_a24);
        } else {
            xadd(point_r1, point_r0, point_r1, point_p);
            xdbl(point_r0, point_r0, curve_a24);
        }
    }
    result = point_r0;
}

static void isogeny(Fp& curve_a, Pt& point_q, const Pt& point_k, int degree_l) {
    Fp curve_a24 = a24_of(curve_a);
    int degree_d = (degree_l - 1) / 2;
    std::vector<Pt> point_vector(degree_d + 2);
    point_vector[1] = point_k;
    if (degree_d >= 2) xdbl(point_vector[2], point_k, curve_a24);
    for (int i = 3; i <= degree_d; i++) xadd(point_vector[i], point_vector[i - 1], point_k, point_vector[i - 2]);
    Fp product_plus = FONE, product_minus = FONE, term_plus = FONE, term_minus = FONE, x_minus, x_plus;
    fsub(x_minus, point_q.X, point_q.Z);
    fadd(x_plus, point_q.X, point_q.Z);
    for (int i = 1; i <= degree_d; i++) {
        Fp sum_val, diff_val, variable_u, variable_v, weight_one, weight_two;
        fadd(sum_val, point_vector[i].X, point_vector[i].Z);
        fsub(diff_val, point_vector[i].X, point_vector[i].Z);
        fmul(product_plus, product_plus, sum_val);
        fmul(product_minus, product_minus, diff_val);
        fmul(variable_u, x_minus, sum_val);
        fmul(variable_v, x_plus, diff_val);
        fadd(weight_one, variable_u, variable_v);
        fsub(weight_two, variable_u, variable_v);
        fmul(term_plus, term_plus, weight_one);
        fmul(term_minus, term_minus, weight_two);
    }
    Fp a_plus, a_minus, numerator, denominator, numerator_val, denominator_val, inverse_val;
    fadd(a_plus, curve_a, FTWO);
    fsub(a_minus, curve_a, FTWO);
    fpow_small(numerator, a_plus, (u64)degree_l);
    fpow_small(denominator, a_minus, (u64)degree_l);
    for (int i = 0; i < 3; i++) {
        fsqr(product_plus, product_plus);
        fsqr(product_minus, product_minus);
    }
    fmul(numerator, numerator, product_plus);
    fmul(denominator, denominator, product_minus);
    fadd(numerator_val, numerator, denominator);
    fsub(denominator_val, numerator, denominator);
    finv(inverse_val, denominator_val);
    fmul(curve_a, numerator_val, inverse_val);
    fadd(curve_a, curve_a, curve_a);
    Fp temp_two, temp_three;
    fsqr(temp_two, term_plus);
    fsqr(temp_three, term_minus);
    fmul(point_q.X, point_q.X, temp_two);
    fmul(point_q.Z, point_q.Z, temp_three);
}

static void action(Fp& output_buffer, const Fp& curve_a0, const int8_t* priv_e0) {
    int8_t exponent[NPR];
    memcpy(exponent, priv_e0, NPR);
    Fp curve_a = curve_a0;
    for (;;) {
        bool has_any = false;
        for (int i = 0; i < NPR; i++)
            if (exponent[i]) { has_any = true; break; }
        if (!has_any) break;
        Fp x_coord = rnd_fp();
        Fp x_squared, temp, legendre_poly;
        fsqr(x_squared, x_coord);
        fmul(temp, curve_a, x_coord);
        fadd(temp, temp, x_squared);
        fadd(temp, temp, FONE);
        fmul(legendre_poly, temp, x_coord);
        int legendre_val = fleg(legendre_poly);
        if (legendre_val == 0) continue;
        std::vector<int> index_list;
        for (int i = 0; i < NPR; i++)
            if (exponent[i] != 0 && ((exponent[i] > 0) == (legendre_val > 0))) index_list.push_back(i);
        if (index_list.empty()) continue;
        bool in_subset[NPR];
        for (int i = 0; i < NPR; i++) in_subset[i] = false;
        for (size_t j = 0; j < index_list.size(); j++) in_subset[index_list[j]] = true;
        u64 scalar_key[8];
        memset(scalar_key, 0, sizeof scalar_key);
        scalar_key[0] = 4;
        for (int i = 0; i < NPR; i++)
            if (!in_subset[i]) mul_small(scalar_key, (u64)PR[i]);
        Fp curve_a24 = a24_of(curve_a);
        Pt point_p, point_q;
        point_p.X = x_coord;
        point_p.Z = FONE;
        xmul(point_q, point_p, scalar_key, curve_a24);
        std::vector<int> active_list = index_list;
        for (size_t idx = 0; idx < index_list.size(); idx++) {
            int i = index_list[idx];
            memset(scalar_key, 0, sizeof scalar_key);
            scalar_key[0] = 1;
            for (size_t j = 0; j < active_list.size(); j++)
                if (active_list[j] != i) mul_small(scalar_key, (u64)PR[active_list[j]]);
            curve_a24 = a24_of(curve_a);
            Pt point_r;
            xmul(point_r, point_q, scalar_key, curve_a24);
            if (pt_inf(point_r)) continue;
            isogeny(curve_a, point_q, point_r, PR[i]);
            exponent[i] = (int8_t)(exponent[i] - legendre_val);
            active_list.erase(std::find(active_list.begin(), active_list.end(), i));
        }
    }
    output_buffer = curve_a;
}

static bool validate(const Fp& curve_a) {
    Fp minus_two;
    fsub(minus_two, FZERO, FTWO);
    if (feq(curve_a, FTWO) || feq(curve_a, minus_two)) return false;
    Fp curve_a24 = a24_of(curve_a);
    for (int attempt_index = 0; attempt_index < 24; attempt_index++) {
        Fp x_coord = rnd_fp();
        Pt point_p, point_r;
        point_p.X = x_coord;
        point_p.Z = FONE;
        u64 scalar_key4[8];
        memset(scalar_key4, 0, sizeof scalar_key4);
        scalar_key4[0] = 4;
        xmul(point_r, point_p, scalar_key4, curve_a24);
        u64 divisor_array[8];
        memset(divisor_array, 0, sizeof divisor_array);
        divisor_array[0] = 1;
        for (int i = 0; i < NPR; i++) {
            u64 scalar_key[8];
            memset(scalar_key, 0, sizeof scalar_key);
            scalar_key[0] = 1;
            for (int j = 0; j < NPR; j++)
                if (j != i) mul_small(scalar_key, (u64)PR[j]);
            Pt point_q;
            xmul(point_q, point_r, scalar_key, curve_a24);
            if (!pt_inf(point_q)) {
                Pt point_t;
                u64 scalar_key_l[8];
                memset(scalar_key_l, 0, sizeof scalar_key_l);
                scalar_key_l[0] = (u64)PR[i];
                xmul(point_t, point_q, scalar_key_l, curve_a24);
                if (!pt_inf(point_t)) return false;
                mul_small(divisor_array, (u64)PR[i]);
            }
        }
        int bit_length = 0;
        for (int i = 511; i >= 0; i--)
            if ((divisor_array[i >> 6] >> (i & 63)) & 1) { bit_length = i + 1; break; }
        if (bit_length >= 259) return true;
    }
    return false;
}

static void fp_to_bytes(const Fp& operand_a, u8* output_buffer) {
    Fp result = frommont(operand_a);
    for (int i = 0; i < 8; i++)
        for (int b = 0; b < 8; b++) output_buffer[i * 8 + b] = (u8)(result.v[i] >> (8 * b));
}

static bool fp_from_bytes(const u8* input_buffer, Fp& operand_a) {
    Fp result;
    for (int i = 0; i < 8; i++) {
        u64 word_value = 0;
        for (int b = 0; b < 8; b++) word_value |= (u64)input_buffer[i * 8 + b] << (8 * b);
        result.v[i] = word_value;
    }
    if (ge_p(result.v)) return false;
    operand_a = tomont(result);
    return true;
}

static void fp_words(const Fp& operand_a, u32* word_array) {
    Fp result = frommont(operand_a);
    for (int i = 0; i < 8; i++) {
        word_array[2 * i] = (u32)result.v[i];
        word_array[2 * i + 1] = (u32)(result.v[i] >> 32);
    }
}

static bool sha256(const u8* data_ptr, size_t data_len, u8* output_buffer) {
    unsigned int out_length = 0;
    return EVP_Digest(data_ptr, data_len, output_buffer, &out_length, EVP_sha256(), nullptr) == 1 && out_length == 32;
}

static bool gcm_seal(const u8* encryption_key, const u8* initialization_vector, const u8* additional_data, size_t aad_length, const u8* plaintext, size_t plaintext_len,
                     u8* ciphertext, u8* auth_tag) {
    EVP_CIPHER_CTX* cipher_context = EVP_CIPHER_CTX_new();
    if (!cipher_context) return false;
    int len_val = 0;
    bool success_flag = EVP_EncryptInit_ex(cipher_context, EVP_aes_256_gcm(), nullptr, nullptr, nullptr) == 1 &&
              EVP_CIPHER_CTX_ctrl(cipher_context, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr) == 1 &&
              EVP_EncryptInit_ex(cipher_context, nullptr, nullptr, encryption_key, initialization_vector) == 1 &&
              EVP_EncryptUpdate(cipher_context, nullptr, &len_val, additional_data, (int)aad_length) == 1;
    if (success_flag && plaintext_len) success_flag = EVP_EncryptUpdate(cipher_context, ciphertext, &len_val, plaintext, (int)plaintext_len) == 1 && (size_t)len_val == plaintext_len;
    if (success_flag) success_flag = EVP_EncryptFinal_ex(cipher_context, ciphertext + plaintext_len, &len_val) == 1;
    if (success_flag) success_flag = EVP_CIPHER_CTX_ctrl(cipher_context, EVP_CTRL_GCM_GET_TAG, 16, auth_tag) == 1;
    EVP_CIPHER_CTX_free(cipher_context);
    return success_flag;
}

static bool gcm_open(const u8* encryption_key, const u8* initialization_vector, const u8* additional_data, size_t aad_length, const u8* ciphertext, size_t plaintext_len,
                     const u8* auth_tag, u8* plaintext) {
    EVP_CIPHER_CTX* cipher_context = EVP_CIPHER_CTX_new();
    if (!cipher_context) return false;
    int len_val = 0;
    u8 tag_buffer[16];
    memcpy(tag_buffer, auth_tag, 16);
    bool success_flag = EVP_DecryptInit_ex(cipher_context, EVP_aes_256_gcm(), nullptr, nullptr, nullptr) == 1 &&
              EVP_CIPHER_CTX_ctrl(cipher_context, EVP_CTRL_GCM_SET_IVLEN, 12, nullptr) == 1 &&
              EVP_DecryptInit_ex(cipher_context, nullptr, nullptr, encryption_key, initialization_vector) == 1 &&
              EVP_DecryptUpdate(cipher_context, nullptr, &len_val, additional_data, (int)aad_length) == 1;
    if (success_flag && plaintext_len) success_flag = EVP_DecryptUpdate(cipher_context, plaintext, &len_val, ciphertext, (int)plaintext_len) == 1 && (size_t)len_val == plaintext_len;
    if (success_flag) success_flag = EVP_CIPHER_CTX_ctrl(cipher_context, EVP_CTRL_GCM_SET_TAG, 16, tag_buffer) == 1;
    if (success_flag) {
        u8 dummy_buffer[16];
        success_flag = EVP_DecryptFinal_ex(cipher_context, dummy_buffer, &len_val) == 1;
    }
    EVP_CIPHER_CTX_free(cipher_context);
    return success_flag;
}

static bool derive_key(const std::vector<u32>& vector_data, u32 dimension_val, u8* encryption_key) {
    std::vector<u8> byte_vector;
    byte_vector.reserve(vector_data.size() * 4 + 4);
    for (size_t i = 0; i < vector_data.size(); i++)
        for (int b = 0; b < 4; b++) byte_vector.push_back((u8)(vector_data[i] >> (8 * b)));
    for (int b = 0; b < 4; b++) byte_vector.push_back((u8)(dimension_val >> (8 * b)));
    return sha256(byte_vector.data(), byte_vector.size(), encryption_key);
}

static bool sendall(int socket_descriptor, const u8* buffer_ptr, size_t length) {
    while (length) {
        ssize_t bytes_sent = send(socket_descriptor, buffer_ptr, length, MSG_NOSIGNAL);
        if (bytes_sent <= 0) return false;
        buffer_ptr += bytes_sent;
        length -= (size_t)bytes_sent;
    }
    return true;
}

static bool recvall(int socket_descriptor, u8* buffer_ptr, size_t length) {
    while (length) {
        ssize_t bytes_received = recv(socket_descriptor, buffer_ptr, length, 0);
        if (bytes_received <= 0) return false;
        buffer_ptr += bytes_received;
        length -= (size_t)bytes_received;
    }
    return true;
}

static std::string to_hex(const u8* data_ptr, size_t length) {
    static const char* hex_chars = "0123456789abcdef";
    std::string string_val;
    for (size_t i = 0; i < length; i++) {
        string_val.push_back(hex_chars[data_ptr[i] >> 4]);
        string_val.push_back(hex_chars[data_ptr[i] & 15]);
    }
    return string_val;
}

static bool from_hex(const std::string& string_val, u8* output_buffer, size_t length) {
    if (string_val.size() != length * 2) return false;
    for (size_t i = 0; i < length; i++) {
        int hex_vals[2];
        for (int j = 0; j < 2; j++) {
            char char_val = string_val[2 * i + j];
            if (char_val >= '0' && char_val <= '9') hex_vals[j] = char_val - '0';
            else if (char_val >= 'a' && char_val <= 'f') hex_vals[j] = char_val - 'a' + 10;
            else if (char_val >= 'A' && char_val <= 'F') hex_vals[j] = char_val - 'A' + 10;
            else return false;
        }
        output_buffer[i] = (u8)(hex_vals[0] * 16 + hex_vals[1]);
    }
    return true;
}

static void put32(u8* buffer_ptr, u32 value_32) {
    for (int i = 0; i < 4; i++) buffer_ptr[i] = (u8)(value_32 >> (8 * i));
}

static u32 get32(const u8* buffer_ptr) {
    u32 value_32 = 0;
    for (int i = 0; i < 4; i++) value_32 |= (u32)buffer_ptr[i] << (8 * i);
    return value_32;
}

static void put64(u8* buffer_ptr, u64 value_64) {
    for (int i = 0; i < 8; i++) buffer_ptr[i] = (u8)(value_64 >> (8 * i));
}

static u64 get64(const u8* buffer_ptr) {
    u64 value_64 = 0;
    for (int i = 0; i < 8; i++) value_64 |= (u64)buffer_ptr[i] << (8 * i);
    return value_64;
}

static u32 rl32(u32 val_x, u32 val_r) { return (val_x << val_r) | (val_x >> (32u - val_r)); }

static u32 mw(u32 val_x) {
    val_x ^= val_x >> 16;
    val_x *= 0x7feb352dU;
    val_x ^= val_x >> 15;
    val_x *= 0x846ca68bU;
    val_x ^= val_x >> 16;
    return val_x;
}

static void cpu_vector(const u32* seed_array, u32 dimension_val, std::vector<u32>& output_vector) {
    std::vector<u32> vector_a(dimension_val), vector_b(dimension_val);
    for (u32 i = 0; i < dimension_val; i++) {
        u32 accumulator = 0x9E3779B9u ^ (i * 0x85EBCA6Bu) ^ dimension_val;
        for (u32 j = 0; j < 16; j++) accumulator = mw(accumulator ^ seed_array[j]) + rl32(accumulator, j + 1u);
        vector_a[i] = accumulator;
    }
    for (u32 r = 0; r < ROUNDS; r++) {
        for (u32 i = 0; i < dimension_val; i++) {
            u32 val_x = vector_a[i], val_y = vector_a[(i + 1u) % dimension_val], val_z = vector_a[(i + dimension_val - 1u) % dimension_val], val_w = vector_a[(i * 5u + 3u + r * 131u) % dimension_val];
            vector_b[i] = mw(val_x + rl32(val_y, 7u) + (val_z ^ rl32(val_w, 19u)) + r);
        }
        vector_a.swap(vector_b);
    }
    output_vector = vector_a;
}

static bool handle(int client_socket, const int8_t* priv_array, const u8* server_pk, FILE* output_file) {
    u8 packet_header[88];
    if (!recvall(client_socket, packet_header, 88)) return false;
    Fp client_public_key;
    if (!fp_from_bytes(packet_header, client_public_key)) return false;
    u32 dimension_val = get32(packet_header + 64);
    u64 data_len = get64(packet_header + 80);
    if (dimension_val < 1024 || dimension_val > 8192 || data_len > ((u64)64 << 20)) return false;
    if (!validate(client_public_key)) return false;
    std::vector<u8> ciphertext((size_t)data_len), plaintext((size_t)data_len);
    u8 auth_tag[16];
    if (data_len && !recvall(client_socket, ciphertext.data(), (size_t)data_len)) return false;
    if (!recvall(client_socket, auth_tag, 16)) return false;
    Fp shared_secret;
    action(shared_secret, client_public_key, priv_array);
    u32 word_array[16];
    fp_words(shared_secret, word_array);
    std::vector<u32> vector_data;
    cpu_vector(word_array, dimension_val, vector_data);
    u8 encryption_key[32];
    if (!derive_key(vector_data, dimension_val, encryption_key)) return false;
    u8 additional_data[132];
    memcpy(additional_data, server_pk, 64);
    memcpy(additional_data + 64, packet_header, 64);
    put32(additional_data + 128, dimension_val);
    if (!gcm_open(encryption_key, packet_header + 68, additional_data, sizeof additional_data, ciphertext.data(), (size_t)data_len, auth_tag, plaintext.data())) return false;
    if (data_len) fwrite(plaintext.data(), 1, (size_t)data_len, output_file);
    fflush(output_file);
    return true;
}

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "Cach dung: %s <port> [file_ra]\n", argv[0]);
        return 1;
    }
    init_params();
    int8_t priv_array[NPR];
    rnd_priv(priv_array);
    Fp server_public_key;
    action(server_public_key, FZERO, priv_array);
    u8 public_key_bytes[64];
    fp_to_bytes(server_public_key, public_key_bytes);
    fprintf(stderr, "Khoa cong khai server: %s\n", to_hex(public_key_bytes, 64).c_str());
    int listen_socket = socket(AF_INET, SOCK_STREAM, 0);
    if (listen_socket < 0) return 1;
    int option_val = 1;
    setsockopt(listen_socket, SOL_SOCKET, SO_REUSEADDR, &option_val, sizeof option_val);
    sockaddr_in server_address;
    memset(&server_address, 0, sizeof server_address);
    server_address.sin_family = AF_INET;
    server_address.sin_addr.s_addr = htonl(INADDR_ANY);
    server_address.sin_port = htons((uint16_t)atoi(argv[1]));
    if (bind(listen_socket, (sockaddr*)&server_address, sizeof server_address) < 0 || listen(listen_socket, 8) < 0) {
        fprintf(stderr, "Khong the lang nghe cong %s\n", argv[1]);
        close(listen_socket);
        return 1;
    }
    fprintf(stderr, "Dang lang nghe cong %s\n", argv[1]);
    for (;;) {
        int client_socket = accept(listen_socket, nullptr, nullptr);
        if (client_socket < 0) continue;
        timeval timeout_val;
        timeout_val.tv_sec = 60;
        timeout_val.tv_usec = 0;
        setsockopt(client_socket, SOL_SOCKET, SO_RCVTIMEO, &timeout_val, sizeof timeout_val);
        u8 status_byte = 0;
        if (sendall(client_socket, public_key_bytes, 64)) {
            FILE* output_file = stdout;
            if (argc > 2) output_file = fopen(argv[2], "wb");
            if (output_file) {
                status_byte = handle(client_socket, priv_array, public_key_bytes, output_file) ? 1 : 0;
                if (output_file != stdout) {
                    fclose(output_file);
                    output_file = nullptr;
                }
            }
            sendall(client_socket, &status_byte, 1);
        }
        fprintf(stderr, status_byte ? "Giai ma thanh cong\n" : "Giai ma that bai\n");
        close(client_socket);
    }
    close(listen_socket);
    return 0;
}