#!/usr/bin/env python3
"""
CSQIT 10.4.5 Operad谱特征值计算
对应附录A.8节数值结果
版本: 10.4.5
"""

import numpy as np
import json
from typing import List, Tuple, Dict
from dataclasses import dataclass
import matplotlib.pyplot as plt
from scipy import sparse
from scipy.sparse.linalg import eigsh

@dataclass
class ColoredOperad:
    """彩色Operad的数值表示"""
    colors: List[str]
    operations: Dict[Tuple[str, ...], List[Dict]]
    
    def to_adjacency_matrix(self) -> np.ndarray:
        """转换为邻接矩阵（颜色间的连接数）"""
        n = len(self.colors)
        color_to_idx = {c: i for i, c in enumerate(self.colors)}
        adj = np.zeros((n, n))
        
        for (inputs, output), ops in self.operations.items():
            if not inputs:
                continue
            for op in ops:
                for inp in inputs:
                    i = color_to_idx[inp]
                    j = color_to_idx[output]
                    adj[i, j] += 1
        
        return adj
    
    def combinatorial_laplacian(self, normalized: bool = True) -> np.ndarray:
        """计算组合拉普拉斯算子"""
        adj = self.to_adjacency_matrix()
        n = adj.shape[0]
        D = np.diag(adj.sum(axis=1))
        
        if normalized:
            D_inv_sqrt = np.diag(1.0 / np.sqrt(np.maximum(D.diagonal(), 1e-10)))
            L = np.eye(n) - D_inv_sqrt @ adj @ D_inv_sqrt
        else:
            L = D - adj
        
        return L

def construct_standard_model_operad() -> ColoredOperad:
    """构建标准模型对应的Operad"""
    colors = [
        'L', 'R', 'Q', 'U', 'D',  # 费米子场
        'W', 'B', 'G',             # 规范玻色子
        'H',                        # 希格斯
        'ψ₁', 'ψ₂', 'ψ₃'            # 三代标记
    ]
    
    operations = {}
    
    # 规范相互作用
    ops_gauge = [
        (('Q', 'Q', 'G'), 'Q'),
        (('L', 'L', 'W'), 'L'),
        (('L', 'L', 'B'), 'L'),
        (('Q', 'Q', 'W'), 'Q'),
    ]
    
    for inputs, output in ops_gauge:
        key = (tuple(inputs), output)
        if key not in operations:
            operations[key] = []
        operations[key].append({'type': 'gauge', 'amplitude': 1.0})
    
    # 汤川耦合（三代结构）
    for i in range(1, 4):
        ops_yukawa = [
            ((f'ψ{i}', 'Q', 'H'), f'ψ{i}'),
            ((f'ψ{i}', 'Q', 'H̅'), f'ψ{i}'),
            ((f'ψ{i}', 'L', 'H'), f'ψ{i}'),
        ]
        for inputs, output in ops_yukawa:
            key = (tuple(inputs), output)
            if key not in operations:
                operations[key] = []
            operations[key].append({'type': 'yukawa', 'generation': i})
    
    # 希格斯自相互作用
    ops_higgs = [
        (('H', 'H', 'H'), 'H'),
        (('H', 'H', 'H', 'H'), 'H'),
    ]
    for inputs, output in ops_higgs:
        key = (tuple(inputs), output)
        operations[key] = [{'type': 'higgs'}]
    
    return ColoredOperad(colors, operations)

def compute_spectrum(operad: ColoredOperad) -> Dict:
    """计算Operad谱"""
    L = operad.combinatorial_laplacian(normalized=True)
    eigenvalues = np.linalg.eigvalsh(L)
    
    return {
        'eigenvalues': eigenvalues.tolist(),
        'min': float(np.min(eigenvalues)),
        'max': float(np.max(eigenvalues)),
        'gap': float(np.min(eigenvalues[eigenvalues > 1e-10])),
        'chi': float(np.max(eigenvalues)),
    }

def monte_carlo_spectrum(n_samples: int = 10000, seed: int = 42) -> Dict:
    """蒙特卡洛采样计算谱的统计分布"""
    np.random.seed(seed)
    
    base_operad = construct_standard_model_operad()
    base_adj = base_operad.to_adjacency_matrix()
    
    chi_samples = []
    
    for _ in range(n_samples):
        noise = np.random.normal(0, 0.01, base_adj.shape)
        perturbed_adj = base_adj * (1 + noise)
        perturbed_adj = np.maximum(perturbed_adj, 0)
        
        D = np.diag(perturbed_adj.sum(axis=1))
        D_inv_sqrt = np.diag(1.0 / np.sqrt(np.maximum(D.diagonal(), 1e-10)))
        L_norm = np.eye(len(perturbed_adj)) - D_inv_sqrt @ perturbed_adj @ D_inv_sqrt
        
        eigvals = np.linalg.eigvalsh(L_norm)
        chi_samples.append(float(np.max(eigvals)))
    
    return {
        'mean': float(np.mean(chi_samples)),
        'std': float(np.std(chi_samples)),
        'q16': float(np.percentile(chi_samples, 16)),
        'q84': float(np.percentile(chi_samples, 84)),
        'q2.5': float(np.percentile(chi_samples, 2.5)),
        'q97.5': float(np.percentile(chi_samples, 97.5)),
        'samples': chi_samples[:1000],
    }

def plot_spectrum(spectrum: Dict, mc_results: Dict):
    """绘制谱分布图"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
    
    # 左图：特征值分布
    eigenvalues = spectrum['eigenvalues']
    ax1.hist(eigenvalues, bins=30, alpha=0.7, color='blue', edgecolor='black')
    ax1.axvline(x=spectrum['chi'], color='red', linestyle='--', 
                label=f'χ = {spectrum["chi"]:.3f}')
    ax1.set_xlabel('特征值')
    ax1.set_ylabel('频数')
    ax1.set_title('拉普拉斯算子特征值分布')
    ax1.legend()
    ax1.grid(True, alpha=0.3)
    
    # 右图：蒙特卡洛分布
    ax2.hist(mc_results['samples'], bins=30, alpha=0.7, color='green', edgecolor='black')
    ax2.axvline(x=mc_results['mean'], color='red', linestyle='-', 
                label=f'均值 = {mc_results["mean"]:.3f}')
    ax2.axvline(x=mc_results['mean'] + mc_results['std'], 
                color='orange', linestyle='--', label='±1σ')
    ax2.axvline(x=mc_results['mean'] - mc_results['std'], 
                color='orange', linestyle='--')
    ax2.set_xlabel('χ(𝒪)')
    ax2.set_ylabel('频数')
    ax2.set_title('蒙特卡洛采样分布 (n=10000)')
    ax2.legend()
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('operad_spectrum.png', dpi=300)
    plt.show()

if __name__ == '__main__':
    print("=" * 60)
    print("CSQIT 10.4.5 Operad谱特征值计算")
    print("=" * 60)
    
    # 构建Operad
    print("\n[1/3] 构建标准模型Operad...")
    operad = construct_standard_model_operad()
    print(f"   颜色数: {len(operad.colors)}")
    print(f"   操作数: {sum(len(ops) for ops in operad.operations.values())}")
    
    # 计算谱
    print("\n[2/3] 计算谱特征值...")
    spectrum = compute_spectrum(operad)
    print(f"   谱范围: [{spectrum['min']:.3f}, {spectrum['max']:.3f}]")
    print(f"   谱隙: {spectrum['gap']:.3f}")
    print(f"   χ(𝒪) = λ_max = {spectrum['chi']:.3f}")
    
    # 蒙特卡洛分析
    print("\n[3/3] 蒙特卡洛分析...")
    mc_results = monte_carlo_spectrum(n_samples=10000)
    print(f"   χ均值 = {mc_results['mean']:.3f}")
    print(f"   χ标准差 = {mc_results['std']:.3f}")
    print(f"   95%置信区间 = [{mc_results['q2.5']:.3f}, {mc_results['q97.5']:.3f}]")
    
    # 绘图
    plot_spectrum(spectrum, mc_results)
    
    # 保存结果
    results = {
        'spectrum': spectrum,
        'monte_carlo': {
            'mean': mc_results['mean'],
            'std': mc_results['std'],
            'q2.5': mc_results['q2.5'],
            'q97.5': mc_results['q97.5'],
        },
        'metadata': {
            'version': '10.4.5',
            'date': '2026-03-14',
            'n_colors': len(operad.colors),
            'n_operations': sum(len(ops) for ops in operad.operations.values())
        }
    }
    
    with open('operad_spectrum.json', 'w') as f:
        json.dump(results, f, indent=2)
    
    print("\n✅ 结果已保存至 operad_spectrum.json")
    print(f"\n最终结果: χ(𝒪) = {mc_results['mean']:.3f} ± {mc_results['std']:.3f}")
    print("=" * 60)