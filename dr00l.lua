-- dr00l.lua

misc = { }

function rprop(x)
    for i = 0, 5 do
        x = x | (x >> (1 << i))
    end
    return x
end

function pboot()
    misc.PTAB = { }
    for i = 0, 255 do
        local j, p = i, 0
        while (i ~= 0) do
            i = i & (i - 1)
            p = p + 1
        end
        misc.PTAB[j] = p
    end
end
pboot()

function pop(x)
    assert(x >= 0)
    local p = 0
    while (x ~= 0) do
        p = p + misc.PTAB[x & 0xff]
        x = x >> 8
    end
    return p
end

function cl2(x)
    assert(x > 0)
    return pop(rprop(x - 1))
end

gf = { POLY = 0x11b }
gf.HIGH = (rprop(gf.POLY) + 1) >> 1

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

function gf.fboot()
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
gf.fboot()

aes = { }

function aes.aesgfboot()
    aes.MUL2 = { }
    aes.MUL3 = { }
    for i = 0, 255 do
        aes.MUL2[i] = gf.mul(i, 2)
        aes.MUL3[i] = gf.mul(i, 3)
    end
end
aes.aesgfboot()

function aes.rol8(x, n)
    return ((x << n) & 0xff) | (x >> (8 - n))
end

function aes.aessboxboot()
    aes.SBOX = { }
    local p, q, r = 1, 1, aes.rol8
    while (true) do
        f = p & 0x80
        p = p ~ ((p << 1) & 0xff)
        if (f ~= 0) then p = p ~ 0x1b end
        for i = 0, 2 do q = q ~ ((q << (1 << i)) & 0xff) end
        if (q & 0x80 ~= 0) then q = q ~ 0x09 end
        aes.SBOX[p] = 0x63 ~ q ~ r(q, 1) ~ r(q, 2) ~ r(q, 3) ~ r(q, 4)
        if (p == 1) then break end
    end
    aes.SBOX[0] = 0x63
end
aes.aessboxboot()

function aes.aesrconboot()
    aes.RCON = { }
    local x = 1
    for i = 1, 255 do
        aes.RCON[i % 255] = x
        x = gf.mul(x, 2)
    end
end
aes.aesrconboot()

-- aes256
aes.rounds     = 14
aes.block_size = 16
aes.key_size   = 32

function aes.setkey(ctx, key)
    assert(#key == 32)
    local xklen = (aes.rounds + 1) * aes.block_size
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
            w[j] = aes.SBOX[w[j]]
        end
        w[0] = w[0] ~ aes.RCON[i]
        for z = 0, 3 do
            for j = 0, 3 do
                w[j] = w[j] ~ xk[p - aes.key_size + j]
            end
            for j = 0, 3 do
                xk[p] = w[j]
                p     = p + 1
            end
        end
        if (p >= xklen) then break end
        for j = 0, 3 do
            w[j] = aes.SBOX[w[j]] ~ xk[p - aes.key_size + j]
        end
        for j = 0, 3 do
            xk[p] = w[j]
            p     = p + 1
        end
        for z = 0, 2 do
            for j = 0, 3 do
                w[j] = w[j] ~ xk[p - aes.key_size + j]
            end
            for j = 0, 3 do
                xk[p] = w[j]
                p     = p + 1
            end
        end
    end
    ctx.exkey = xk
end

function aes.add_round_key(ctx, blk, round)
    local ofs = round << 4
    for i = 0, 15 do
        blk[i] = blk[i] ~ ctx.exkey[ofs + i]
    end
end

function aes.sub_bytes(blk)
    for i = 0, 15 do
        blk[i] = aes.SBOX[blk[i]]
    end
end

function aes.shift_rows(blk)
    blk[1], blk[5], blk[ 9], blk[13] = blk[ 5], blk[ 9], blk[13], blk[ 1]
    blk[2], blk[6], blk[10], blk[14] = blk[10], blk[14], blk[ 2], blk[ 6]
    blk[3], blk[7], blk[11], blk[15] = blk[15], blk[ 3], blk[ 7], blk[11]
end

function aes.mix_columns(blk)
    m2 = aes.MUL2
    m3 = aes.MUL3
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

function aes.encrypt(ctx, blk)
    aes.add_round_key(ctx, blk, 0)
    for round = 1, aes.rounds - 1 do
        aes.sub_bytes(blk)
        aes.shift_rows(blk)
        aes.mix_columns(blk)
        aes.add_round_key(ctx, blk, round)
    end
    aes.sub_bytes(blk)
    aes.shift_rows(blk)
    aes.add_round_key(ctx, blk, aes.rounds)
    return blk
end

function aes.etest(k, p, x)
    local ctx, blk = { }, { }
    assert(#k == 32)
    assert(#p == 16)
    assert(#x == 16)
    for i = 0, 15 do blk[i] = p[i+1] end
    aes.setkey(ctx, k)
    aes.encrypt(ctx, blk)
    for i = 0, 15 do assert(blk[i] == x[i+1]) end
end

function aes.test()
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
    aes.etest(k, p, x)
    p = {
        0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 
    }
    x = {
        0xdd, 0xc6, 0xbf, 0x79, 0x0c, 0x15, 0x76, 0x0d,
        0x8d, 0x9a, 0xeb, 0x6f, 0x9a, 0x75, 0xfd, 0x4e
    }
    aes.etest(k, p, x)
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
    aes.etest(k, p, x)
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
    aes.etest(k, p, x)
    --print("pass")
end
aes.test()

