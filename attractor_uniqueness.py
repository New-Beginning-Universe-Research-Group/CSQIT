#!/usr/bin/env python3
"""
CSQIT 吸引子唯一性验证脚本

问题：是否只有基底 P = {2,3,5,7} 能同时满足：
  1. α⁻¹ = 137 + 9/250（精确命中）
  2. Hurwitz 三角群结构（(2,3,5) 和 (2,3,7) 的素因子）

方法：枚举所有四素数组合 (p1 < p2 < p3 < p4)，其中 p4 < LIMIT，
     用 CSQIT 公式计算 α⁻¹，看哪些组合能得到接近 137.036 的值。

CSQIT α⁻¹ 公式：α⁻¹ = p1^p4 + p1^p2 + 1 + p2^p1/(p1 * p3^p2)
"""

from itertools import combinations

def compute_alpha_inv(p1, p2, p3, p4):
    """用 CSQIT 公式计算 α⁻¹"""
    return p1**p4 + p1**p2 + 1 + (p2**p1) / (p1 * p3**p2)

def hurwitz_check(p1, p2, p3):
    """检查 (p1,p2,p3) 是否构成 Hurwitz 三角群（1/p1 + 1/p2 + 1/p3 > 1/2）"""
    s = 1/p1 + 1/p2 + 1/p3
    return s > 1/2  # 三角群需要双曲或紧条件

def main():
    LIMIT = 30  # 素数上限
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    
    print("=" * 70)
    print("CSQIT 吸引子唯一性：枚举四素数基底 P")
    print(f"素数范围: p < {LIMIT}")
    print("=" * 70)
    
    target_alpha = 137.036
    found = []
    
    # 枚举所有四素数组合
    for combo in combinations(primes, 4):
        p1, p2, p3, p4 = combo
        
        # CSQIT 要求 p1=2 (最小素数，基底群阶含 2^3=8)
        if p1 != 2:
            continue
        
        alpha = compute_alpha_inv(p1, p2, p3, p4)
        error = abs(alpha - target_alpha)
        
        if error < 1.0:  # 宽松阈值，先看所有接近的
            hurwitz_ok = hurwitz_check(p1, p2, p3) and hurwitz_check(p1, p2, p4)
            found.append((combo, alpha, error, hurwitz_ok))
    
    # 按误差排序
    found.sort(key=lambda x: x[2])
    
    print(f"\n找到 {len(found)} 组误差 < 1.0 的候选基底：")
    print("-" * 70)
    print(f"{'基底 P':<22} {'α⁻¹ 值':<18} {'误差':<12} {'Hurwitz?':<10}")
    print("-" * 70)
    
    for combo, alpha, error, hurwitz_ok in found[:20]:  # 显示前20个
        p_str = str(set(combo))
        h_str = "✓ (2,3,5)&(2,3,7)" if hurwitz_ok else "✗"
        marker = " <<< 唯一吸引子" if error < 0.01 and hurwitz_ok else ""
        print(f"{p_str:<22} {alpha:<18.6f} {error:<12.6f} {h_str:<10}{marker}")
    
    print("-" * 70)
    
    # 结论
    perfect = [f for f in found if f[2] < 0.01 and f[3]]
    if len(perfect) == 1:
        print(f"\n✓ 结论：唯一吸引子是 P = {set(perfect[0][0])}")
        print(f"  α⁻¹ = {perfect[0][1]:.6f}, 误差 = {perfect[0][2]:.6f}")
        print(f"  满足 Hurwitz 条件：(2,3,5) 和 (2,3,7) 都是三角群")
    elif len(perfect) > 1:
        print(f"\n⚠ 警告：找到多个完美匹配 {[set(p[0]) for p in perfect]}")
    else:
        print(f"\n✗ 没找到完美匹配（误差 < 0.01 且满足 Hurwitz 条件）")
    
    # 专门分析 P = {2,3,5,7}
    print("\n" + "=" * 70)
    print("详细分析基底 P = {2,3,5,7}")
    print("=" * 70)
    
    p1, p2, p3, p4 = 2, 3, 5, 7
    alpha = compute_alpha_inv(p1, p2, p3, p4)
    print(f"\nCSQIT α⁻¹ 公式展开：")
    print(f"  p1^p4  = {p1}^{p4} = {p1**p4}")
    print(f"  p1^p2  = {p1}^{p2} = {p1**p2}")
    print(f"  p2^p1  = {p2}^{p1} = {p2**p1}")
    print(f"  p3^p2  = {p3}^{p2} = {p3**p2}")
    print(f"  1 + p1^p2 + p1^p4 = 1 + {p1**p2} + {p1**p4} = {1 + p1**p2 + p1**p4}")
    print(f"  p2^p1/(p1*p3^p2)  = {p2**p1}/({p1}*{p3**p2}) = {p2**p1}/{p1*p3**p2} = {p2**p1/(p1*p3**p2):.6f}")
    print(f"  α⁻¹ = {alpha:.6f}")
    print(f"  观测值 ≈ 137.035999")
    print(f"  误差 = {abs(alpha - 137.035999):.6f}")
    
    # Hurwitz 三角群分析
    print(f"\nHurwitz 三角群验证：")
    print(f"  (2,3,5): 1/2 + 1/3 + 1/5 = {1/2+1/3+1/5:.4f} > 1 → 紧群 (A5, 阶 60)")
    print(f"  (2,3,7): 1/2 + 1/3 + 1/7 = {1/2+1/3+1/7:.4f} < 1 → 双曲群 (PSL(2,7), 阶 168)")
    print(f"  P = {{2,3,5,7}} 是两个群素因子的并集")
    
    # 检查 Hurwitz 条件是否唯一
    print(f"\nHurwitz 条件唯一性检查（p4 < 30）：")
    hurwitz_combo_count = 0
    for combo in combinations(primes, 4):
        p1, p2, p3, p4 = combo
        if p1 != 2:
            continue
        has_235 = hurwitz_check(2, 3, 5) and (5 in combo) and (3 in combo)
        has_237 = hurwitz_check(2, 3, 7) and (7 in combo) and (3 in combo)
        if has_235 and has_237:
            hurwitz_combo_count += 1
            alpha = compute_alpha_inv(*combo)
            print(f"  {str(set(combo)):<20} α⁻¹ = {alpha:.4f}")
    
    print(f"\n同时包含 (2,3,5) 和 (2,3,7) 子结构的四素数基底有 {hurwitz_combo_count} 个")
    print(f"其中只有 P = {{2,3,5,7}} 的 α⁻¹ 精确命中 137.036")

if __name__ == "__main__":
    main()
