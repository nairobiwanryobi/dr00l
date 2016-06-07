#!/usr/bin/env lua

-- dr00l.lua

bitbang = { }

function bitbang.rprop(x)
    for i = 0, 5 do
        x = x | (x >> (1 << i))
    end
    return x
end

function bitbang.pboot()
    bitbang.PTAB = { }
    for i = 0, 255 do
        local j, p = i, 0
        while (i ~= 0) do
            i = i & (i - 1)
            p = p + 1
        end
        bitbang.PTAB[j] = p
    end
end
bitbang.pboot()

function bitbang.pop(x)
    assert(x >= 0)
    local p = 0
    while (x ~= 0) do
        p = p + bitbang.PTAB[x & 0xff]
        x = x >> 8
    end
    return p
end

function bitbang.cl2(x)
    assert(x > 0)
    return bitbang.pop(bitbang.rprop(x - 1))
end

gf = { POLY = 0x11b }
gf.HIGH = (bitbang.rprop(gf.POLY) + 1) >> 1

function gf.mul0(x, y)
    prod = 0
    while (y ~= 0) do
        if (y & 1 ~= 0) then prod = prod ~ x end
        x = x << 1
        if (x & gf.HIGH ~= 0) then x = x ~ gf.POLY end
        y = y >> 1
    end
    return prod
end

function gf.isgen(g)
    local x, s = 1, { }
    for i = 0, 254 do
        if (s[x] == 1) then return false end
        s[x] = 1
        x    = gf.mul0(x, g)
    end
    return true
end

function gf.mingen()
    for g = 2, 255 do
        if gf.isgen(g) then return g end
    end
    error("ow")
end

gf.E = { }
gf.L = { }

function gf.add(x, y) return x ~ y end

gf.sub = gf.add

function gf.mul(x, y)
    if ((x == 0) or (y == 0)) then return 0 end
    return gf.E[(gf.L[x] + gf.L[y]) % 255]
end

function gf.div(x, y)
    assert(y > 0)
    if (x == 0) then return 0 end
    return gf.E[(gf.L[x] + 255 - gf.L[y]) % 255]
end

function gf.boot()
    local x, g = 1, gf.mingen()
    for i = 0, 254 do
        gf.E[i] = x
        gf.L[x] = i
        x       = gf.mul0(x, g)
    end
    gf.E[255] = 1
    gf.L[0]   = 0
    if (true) then return end
    for i = 0, 255 do
        for j = 0, 255 do
            assert(gf.mul(i, j) == gf.mul0(i, j))
        end
    end
end
gf.boot()

aes256 = { }
aes256.__index = aes256

function aes256.aesgfboot()
    aes256.MUL2 = { }
    aes256.MUL3 = { }
    for i = 0, 255 do
        aes256.MUL2[i] = gf.mul(i, 2)
        aes256.MUL3[i] = gf.mul(i, 3)
    end
end
aes256.aesgfboot()

function aes256.rol8(x, n)
    return ((x << n) & 0xff) | (x >> (8 - n))
end

function aes256.aessboxboot()
    aes256.SBOX = { }
    local p, q, r = 1, 1, aes256.rol8
    while (true) do
        f = p & 0x80
        p = p ~ ((p << 1) & 0xff)
        if (f ~= 0) then p = p ~ 0x1b end
        for i = 0, 2 do q = q ~ ((q << (1 << i)) & 0xff) end
        if (q & 0x80 ~= 0) then q = q ~ 0x09 end
        aes256.SBOX[p] = 0x63 ~ q ~ r(q, 1) ~ r(q, 2) ~ r(q, 3) ~ r(q, 4)
        if (p == 1) then break end
    end
    aes256.SBOX[0] = 0x63
end
aes256.aessboxboot()

function aes256.aesrconboot()
    aes256.RCON = { }
    local x = 1
    for i = 1, 255 do
        aes256.RCON[i % 255] = x
        x = gf.mul(x, 2)
    end
end
aes256.aesrconboot()

-- aes256
aes256.rounds     = 14
aes256.block_size = 16
aes256.key_size   = 32

function aes256:setkey(key)
    assert(#key == 32)
    local xklen = (self.rounds + 1) * self.block_size
    local p, xk, w = 32, { }, { }
    for i = 0, 31 do
        xk[i] = key[i+1]
        assert(xk[i] ~= nil)
    end
    for i = 0, 3 do
        w[i] = xk[p - 4 + i]
    end
    for i = 1, 10 do
        w[0], w[1], w[2], w[3] = w[1], w[2], w[3], w[0]
        for j = 0, 3 do
            w[j] = self.SBOX[w[j]]
        end
        w[0] = w[0] ~ self.RCON[i]
        for z = 0, 3 do
            for j = 0, 3 do
                w[j] = w[j] ~ xk[p - self.key_size + j]
            end
            for j = 0, 3 do
                xk[p] = w[j]
                p     = p + 1
            end
        end
        if (p >= xklen) then break end
        for j = 0, 3 do
            w[j] = self.SBOX[w[j]] ~ xk[p - self.key_size + j]
        end
        for j = 0, 3 do
            xk[p] = w[j]
            p     = p + 1
        end
        for z = 0, 2 do
            for j = 0, 3 do
                w[j] = w[j] ~ xk[p - self.key_size + j]
            end
            for j = 0, 3 do
                xk[p] = w[j]
                p     = p + 1
            end
        end
    end
    self.exkey = xk
end

function aes256:add_round_key(blk, round)
    local ofs = round << 4
    for i = 0, 15 do
        blk[i] = blk[i] ~ self.exkey[ofs + i]
    end
end

function aes256:sub_bytes(blk)
    for i = 0, 15 do
        blk[i] = self.SBOX[blk[i]]
    end
end

function aes256:shift_rows(blk)
    blk[1], blk[5], blk[ 9], blk[13] = blk[ 5], blk[ 9], blk[13], blk[ 1]
    blk[2], blk[6], blk[10], blk[14] = blk[10], blk[14], blk[ 2], blk[ 6]
    blk[3], blk[7], blk[11], blk[15] = blk[15], blk[ 3], blk[ 7], blk[11]
end

function aes256:mix_columns(blk)
    m2 = self.MUL2
    m3 = self.MUL3
    for col = 0, 15, 4 do
        v0         = blk[col]
        v1         = blk[col+1]
        v2         = blk[col+2]
        v3         = blk[col+3]
        blk[col  ] = m2[v0] ~ v3 ~ v2 ~ m3[v1]
        blk[col+1] = m2[v1] ~ v0 ~ v3 ~ m3[v2]
        blk[col+2] = m2[v2] ~ v1 ~ v0 ~ m3[v3]
        blk[col+3] = m2[v3] ~ v2 ~ v1 ~ m3[v0]
    end
end

function aes256:bencrypt(blk)
    self:add_round_key(blk, 0)
    for round = 1, self.rounds - 1 do
        self:sub_bytes(blk)
        self:shift_rows(blk)
        self:mix_columns(blk)
        self:add_round_key(blk, round)
    end
    self:sub_bytes(blk)
    self:shift_rows(blk)
    self:add_round_key(blk, aes256.rounds)
    return blk
end

function aes256:encrypt(p)
    local b, c = { }, ""
    assert(#p == 16)
    for i = 0, 15 do b[i] = string.byte(p, i+1) end
    self:bencrypt(b)
    for i = 0, 15 do c = c .. string.char(b[i]) end
    return c
end

function aes256.new(key)
    local self = setmetatable({ }, aes256)
    self:setkey(key)
    return self
end

function aes256.etest(k, p, x)
    local ctx, blk = aes256.new(k), { }
    assert(#k == 32)
    assert(#p == 16)
    assert(#x == 16)
    for i = 0, 15 do blk[i] = p[i+1] end
    ctx:bencrypt(blk)
    for i = 0, 15 do assert(blk[i] == x[i+1]) end
end

function aes256.test()
    local k = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 
    }
    local p = {
        0x01, 0x47, 0x30, 0xf8, 0x0a, 0xc6, 0x25, 0xfe,
        0x84, 0xf0, 0x26, 0xc6, 0x0b, 0xfd, 0x54, 0x7d
    }
    local x = {
        0x5c, 0x9d, 0x84, 0x4e, 0xd4, 0x6f, 0x98, 0x85,
        0x08, 0x5e, 0x5d, 0x6a, 0x4f, 0x94, 0xc7, 0xd7
    }
    aes256.etest(k, p, x)
    p = {
        0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 
    }
    x = {
        0xdd, 0xc6, 0xbf, 0x79, 0x0c, 0x15, 0x76, 0x0d,
        0x8d, 0x9a, 0xeb, 0x6f, 0x9a, 0x75, 0xfd, 0x4e
    }
    aes256.etest(k, p, x)
    k = {
        0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 
    }
    p = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 
    }
    x = {
        0xe3, 0x5a, 0x6d, 0xcb, 0x19, 0xb2, 0x01, 0xa0,
        0x1e, 0xbc, 0xfa, 0x8a, 0xa2, 0x2b, 0x57, 0x59
    }
    aes256.etest(k, p, x)
    k = {
        0xc4, 0x7b, 0x02, 0x94, 0xdb, 0xbb, 0xee, 0x0f,
        0xec, 0x47, 0x57, 0xf2, 0x2f, 0xfe, 0xee, 0x35,
        0x87, 0xca, 0x47, 0x30, 0xc3, 0xd3, 0x3b, 0x69,
        0x1d, 0xf3, 0x8b, 0xab, 0x07, 0x6b, 0xc5, 0x58
    }
    x = {
        0x46, 0xf2, 0xfb, 0x34, 0x2d, 0x6f, 0x0a, 0xb4,
        0x77, 0x47, 0x6f, 0xc5, 0x01, 0x24, 0x2c, 0x5f
    }
    aes256.etest(k, p, x)
    --print("pass")
end
aes256.test()

sha512 = {
    block_size  = 128,
    digest_size = 64,
    init_const  = {
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
    },
    round_const = {
        0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f,
        0xe9b5dba58189dbbc, 0x3956c25bf348b538, 0x59f111f1b605d019,
        0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242,
        0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
        0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
        0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3,
        0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65, 0x2de92c6f592b0275,
        0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
        0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f,
        0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
        0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc,
        0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
        0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6,
        0x92722c851482353b, 0xa2bfe8a14cf10364, 0xa81a664bbc423001,
        0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
        0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
        0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99,
        0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb,
        0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc,
        0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
        0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915,
        0xc67178f2e372532b, 0xca273eceea26619c, 0xd186b8c721c0c207,
        0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba,
        0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
        0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
        0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a,
        0x5fcb6fab3ad6faec, 0x6c44198c4a475817
    }
}

sha512.__index = sha512

function sha512.new()
    local self = setmetatable({ }, sha512)
    self.digest_  = { } -- 0..7 of uint64
    self.count_lo = 0   -- uint32
    self.count_hi = 0   -- uint32
    self.data     = { } -- 0..block_size-1 of uint8
    self.local_   = 0   -- int
    for i = 0, (self.digest_size >> 3)-1 do
        self.digest_[i] = self.init_const[i+1]
    end
    for i = 0, self.block_size-1 do self.data[i] = 0 end
    return self
end

function sha512:pack128(W)
    local k = 0
    for i = 0, 15 do
        local z = 0
        for j = 0, 7 do
            z = z << 8
            z = z | self.data[k]
            k = k + 1
        end
        W[i] = z
    end
end

MASK64 = 0xffffffffffffffff

function sha512:ror64(x, n)
    x = x & MASK64
    n = n & 0x3f
    return (x >> n) | ((x << (64 - n)) & MASK64)
end

function sha512:Ch (x, y, z) return z ~ (x & (y ~ z)) end
function sha512:Maj(x, y, z) return ((x | y) & z) | (x & y) end
function sha512:S  (x, n)    return self:ror64(x, n) end
function sha512:R  (x, n)    return (x & MASK64) >> (n & 0x3f) end
function sha512:Sigma0(x)
    return self:S(x, 28) ~ self:S(x, 34) ~ self:S(x, 39)
end
function sha512:Sigma1(x)
    return self:S(x, 14) ~ self:S(x, 18) ~ self:S(x, 41)
end
function sha512:Gamma0(x)
    return self:S(x, 1) ~ self:S(x, 8) ~ self:R(x, 7)
end
function sha512:Gamma1(x)
    return self:S(x, 19) ~ self:S(x, 61) ~ self:R(x, 6)
end

function sha512:roll(S)
    local t = S[7]
    for i = 7, 1, -1 do
        S[i] = S[i-1]
    end
    S[0] = t
end

function sha512:transform()
    local S = { } -- 0..7  of uint64
    local W = { } -- 0..79 of uint64
    local t0, t1  -- uint64
    local a, b, c, d, e, f, g, h
    self:pack128(W)
    for i = 16, 79 do
        W[i] = self:Gamma1(W[i-2]) + W[i-7] + self:Gamma0(W[i-15]) + W[i-16]
    end
    for i = 0, 7 do S[i] = self.digest_[i] end
    for i = 0, 79 do
        a = S[0]; b = S[1]; c = S[2]; d = S[3]
        e = S[4]; f = S[5]; g = S[6]; h = S[7]
        t0   = h + self:Sigma1(e) + self:Ch(e, f, g) + self.round_const[i+1] + W[i]
        t1   = self:Sigma0(a) + self:Maj(a, b, c)
        S[3] = S[3] + t0
        S[7] = t0 + t1
        self:roll(S)
    end
    for i = 0, 7 do
        self.digest_[i] = self.digest_[i] + S[i]
    end
end

function sha512:update(s)
    local b = { }
    for i = 1, #s do
        b[i-1] = string.byte(s, i)
    end
    self:bupdate(b)
end

function sha512:bupdate(b)
    local cnt, bp = #b + 1, 0
    local clo = (self.count_lo + (cnt << 3)) & 0xffffffff
    if clo < self.count_lo then
        self.count_hi = self.count_hi + 1
    end
    self.count_lo = clo
    self.count_hi = self.count_hi + (cnt >> 29)
    if self.local_ then
        local i = self.block_size - self.local_
        if i > cnt then i = cnt end
        for j = 0, i-1 do
            self.data[self.local_+j] = b[j]
        end
        cnt         = cnt - i
        bp          = bp + i
        self.local_ = self.local_ + i
        if self.local_ == self.block_size then
            self:transform()
        else
            return
        end
    end
    while cnt >= self.block_size do
        for i = 0, self.block_size-1 do
            self.data[i] = b[bp+i]
        end
        bp  = bp + self.block_size
        cnt = cnt - self.block_size
        self:transform()
    end
    if cnt ~= 0 then
        for i = 0, cnt-1 do
            self.data[i] = b[bp+i]
        end
    end
    self.local_ = cnt
end

function sha512:bdigest()
    local digest = { }
    local count  = (self.count_lo >> 3) & 0x7f
    self.data[count] = 0x80
    count = count + 1
    if count > (self.block_size - 16) then
        for i = 0, self.block_size - count - 1 do
            self.data[count + i] = 0
        end
        self:transform()
        for i = 0, self.block_size - 16 - 1 do
            self.data[i] = 0
        end
    else
        for i = 0, self.block_size - 16 - count - 1 do
            self.data[count+i] = 0
        end
    end
    for i = 112, 119 do self.data[i] = 0 end
    for i = 120, 123 do
        self.data[i] = (self.count_hi >> ((123 - i) << 3)) & 0xff
    end
    for i = 124, 127 do
        self.data[i] = (self.count_lo >> ((127 - i) << 3)) & 0xff
    end
    self:transform()
    local p = 0
    for i = 0, 7 do
        local x = self.digest_[i]
        for j = 7, 0, -1 do
            digest[p+j] = x & 0xff
            x = x >> 8
        end
        p = p + 8
    end
    return digest
end

function sha512:digest()
    local s, d = "", self:bdigest()
    for i = 0, self.digest_size-1 do
        s = s .. string.char(d[i])
    end
    return s
end

function sha512:hexdigest()
    local s, d = "", self:bdigest()
    for i = 0, #d do
        s = s .. string.format("%02x", d[i])
    end
    return s
end

function sha512.test()
    h = sha512.new()
    h:update("abc")
    assert(h:hexdigest() == 'ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f')
end
sha512.test()

hmac512 = {
    block_size  = sha512.block_size,
    digest_size = sha512.digest_size
}
hmac512.__index = hmac512

function hmac512.xors(s1, s2)
    local r = ""
    assert(#s1 == #s2)
    for i = 1, #s1 do
        r = r .. string.char(string.byte(s1, i) ~ string.byte(s2, i))
    end
    return r
end

function hmac512.new(key)
    local self = { }
    local h, ipad, opad
    setmetatable(self, hmac512)
    if #key > sha512.block_size then
        h = sha512.new()
        h:update(key)
        key = h:digest()
    end
    key  = key .. string.rep("\x00", sha512.block_size - #key)
    opad = hmac512.xors(key, string.rep(string.char(0x5c), sha512.block_size))
    ipad = hmac512.xors(key, string.rep(string.char(0x36), sha512.block_size))
    self.opad = opad
    self.h    = sha512.new()
    self.h:update(ipad)
    return self
end

function hmac512:bupdate(b)
    self.h:bupdate(b)
end

function hmac512:update(s)
    self.h:update(s)
end

function hmac512:outer()
    local h = sha512.new()
    h:update(self.opad)
    h:update(self.h:digest())
    return h
end

function hmac512:digest()
    return self:outer():digest()
end

function hmac512:hexdigest()
    return self:outer():hexdigest()
end

function hmac512.test()
    local k, m, x, h
    k = "abc"
    m = "abc"
    x = "1a97e05c35e6727690dfdf2e8079b34fefabf15236abc9170dccdcf5623e4c5ce72a446842bd7607186c9e3f21c0a0edf6ab6c5ec8304a1f969c20c1455e9b7c"
    h = hmac512.new(k); h:update(m); assert(h:hexdigest() == x)
    k = "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"
    m = "hello"
    x = "d9088a96da6f69720f98b60ffc1c0b3e59a6a62cab4c0a087da2420f7aed793fa8467c438f26f4570271f5d600ff2f06a3da3019a2ed99d184a890259e7be524"
    h = hmac512.new(k); h:update(m); assert(h:hexdigest() == x)
    k = "hello"
    m = "abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd"
    x = "e6aa90bd6b1a2504c9c8b3b26bfc8cb85306715fc371351a8db6bb81d28e7f72550a64aa08dea9ea7952322d867e6a8ee29b337b81ed08c49a9c611d70691c12"
    h = hmac512.new(k); h:update(m); assert(h:hexdigest() == x)
end
hmac512.test()

pbkdf2 = { xors = hmac512.xors }
pbkdf2.__index = pbkdf2

function pbkdf2.mac(key, msg)
    local m = hmac512.new(key)
    m:update(msg)
    return m:digest()
end

function pbkdf2.pbkdf2(password, salt, count, dklen)
    local r, i = "", 1
    local t, u
    while #r < dklen do
        t = pbkdf2.mac(password, salt .. string.pack(">I", i))
        u = t
        for j = 1, count-1 do
            u = pbkdf2.mac(password, u)
            t = pbkdf2.xors(t, u)
        end
        r = r .. t
        i = i + 1
    end
    return string.sub(r, 1, dklen)
end

function pbkdf2.tohex(s)
    local r = ""
    for i = 1, #s do r = r .. string.format("%02x", string.byte(s, i)) end
    return r
end

function pbkdf2.test()
    local s, h
    s = pbkdf2.tohex(pbkdf2.pbkdf2("password", "NaCL", 1, hmac512.digest_size))
    assert(s == "73decfa58aa2e84f94771a75736bb88bd3c7b38270cfb50cb390ed78b305656af8148e52452b2216b2b8098b761fc6336060a09f76415e9f71ea47f9e9064306")
    s = pbkdf2.tohex(pbkdf2.pbkdf2("pass\x00word", "sa\x00lt", 1, hmac512.digest_size))
    assert(s == "71a0ec842abd5c678bcfd145f09d83522f93361560563c4d0d63b88329871090e76604a49af08fe7c9f57156c8790996b20f06bc535e5ab5440df7e878296fa7")
    s = pbkdf2.tohex(pbkdf2.pbkdf2("passwordPASSWORDpassword", "salt\x00\x00\x00", 50, hmac512.digest_size))
    assert(s == "016871a4c4b75f96857fd2b9f8ca28023b30ee2a39f5adcac8c9375f9bda1ccd1b6f0b2fc3adda505412e79d890056c62e524c7d51154b1a8534575bd02dee39")
end
pbkdf2.test()

rng = { NITER = 256 }
rng.__index = rng

function rng.rng_()
    local fp = io.open("/dev/urandom")
    local b
    while true do
        b = fp:read(256)
        for i = 1, #b do
            coroutine.yield(string.byte(b, i))
        end
    end
end
rng.rng = coroutine.wrap(rng.rng_)

function rng.prng(password, salt, ident)
    local b0  = string.pack(">II", 0x80000000, ident)
    local seq = 0
    local key = pbkdf2.pbkdf2(password, salt, rng.NITER, aes256.key_size)
    local k   = { }
    for i = 1, #key do k[i] = string.byte(key, i) end
    local C   = aes256.new(k)
    local f   = function()
        local p, c
        while true do
            seq = seq + 1
            p   = b0 .. string.pack(">J", seq)
            c   = C:encrypt(p)
            for i = 1, #c do coroutine.yield(string.byte(c, i)) end
        end
    end
    return coroutine.wrap(f)
end

function rng.test()
    local g = rng.prng("password", "salt", 0x100)
    local x = {
        0x44,  0x8f,  0x79,  0x9e,  0x05,  0xba,  0xde,  0x04, 
        0x0c,  0xeb,  0x30,  0x9f,  0x23,  0x93,  0x3e,  0x04, 
        0xcc,  0xa7,  0xed,  0x9a,  0xd9,  0xa0,  0xb4,  0xb5, 
        0xec,  0xc2,  0x3c,  0x19,  0xba,  0x02,  0x1d,  0xe4, 
    }
    for i = 1, #x do assert(g() == x[i]) end
end
--rng.test()

rng.RAN = { }

function rng.ran(n, g)
    if n == 1 then return 0 end
    assert(n > 1)
    local B, S, L, z
    if rng.RAN[n] == nil then
        local b, N, d
        b = bitbang.cl2(n)
        B = (b + 7) >> 3
        N = 1 << (B << 3)
        S = N // n
        d = N %  n
        L = N -  d
        rng.RAN[n] = { B, S, L }
    end
    z = rng.RAN[n]
    B, S, L = z[1], z[2], z[3]
    while true do
        z = 0
        for i = 1, B do
            z = z << 8
            z = z |  g()
        end
        if z < L then return z // S end
    end
end



