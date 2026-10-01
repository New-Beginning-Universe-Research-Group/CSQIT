# CSQIT 关键常数的 2-adic 分解
numbers = {
    "closure[0]": 8,
    "closure[1]": 64,
    "closure[2]": 420,
    "closure[3]": 840,
    "closure[4]": 1680,
    "closure[5]": 3360,
    "closure[6]": 6720,
    "closure[7]": 13440,
    "e4": 210,
    "totalClosure": 420,
    "PSL(2,7)": 168,
    "A4": 12,
    "A5": 60,
    "N": 420,
    "Fin8_closure": 64,
    "genetic_code": 64,
    "SU3_gen": 8,
    "e1=17": 17,
    "289=17²": 289,
    "9": 9,
    "137": 137,
    "14388780": 14388780,
}
print(f"{'常数':<20} {'值':>10}  v₂  分解")
print("-" * 55)
for name, n in numbers.items():
    v2 = 0
    x = n
    while x % 2 == 0:
        v2 += 1
        x //= 2
    print(f"{name:<20} {n:>10}  {v2:>2}  2^{v2} × {x}")

print("\n=== 核心模式 ===")
print(f"纯 2 的幂 (v₂ = log₂ n): closure[0]=8=2³, closure[1]=64=2⁶")
print(f"closure[n] 对 n≥2: v₂ = n, 奇数核心 = 105 = 3×5×7 = e₄/2")
print(f"e₄ = 210 = 2×105 → v₂=1")
print(f"totalClosure = 420 = 2²×105 → v₂=2")
print(f"N = 2×e₄ = 2²×105 = totalClosure → v₂=2")
print(f"105 = P \\ {2} → 基底去掉唯一偶素数")
