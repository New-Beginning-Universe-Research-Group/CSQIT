# CSQIT 10.4.5 教程

## 目录
1. [项目简介](#项目简介)
2. [快速开始](#快速开始)
3. [核心概念](#核心概念)
4. [公理体系](#公理体系)
5. [实例化示例](#实例化示例)
6. [形式化示例](#形式化示例)
7. [下一步](#下一步)

---

## 项目简介

**CSQIT** (Causal Structure Quantum Information Theory) 是一个在 **Lean 4** 中形式化的量子引力理论项目。

### 核心理论成果

| 成果 | 状态 |
|------|------|
| `input_must_be_empty` | ✅ 已证明 |
| `nonTrivialFinModel` | ✅ 已构造 |
| `axiomD_independent_of_AB` | ✅ 已证明 |
| `axiomD_independent_of_ABC` | 📌 开放问题 |

### 版本信息
- **版本**: 10.5 (Enhanced Edition)
- **日期**: 2026-06-23
- **编译状态**: Core 模块编译通过（编译计数取决于 mathlib 版本）

---

## 快速开始

### 环境要求
- Lean 4 (v4.29.0-rc6)
- Lake 构建系统

### 编译项目
```bash
# 在 WSL 环境中
cd ~/CSQIT_Project
lake build

# 或编译特定模块
lake build Core.Theorems
```

### 查看编译状态
```bash
lake build 2>&1 | grep -E '(error|Build completed)'
```

---

## 核心概念

### 1. 关系元 (Relation Element)
类型 `M` 代表离散时空中的基本因果实体。

```lean
-- 在 FinModels.lean 中
-- M = Fin 2 = {0, 1}
-- 这是一个最简单的非平凡模型
```

### 2. 规则 (Rule)
类型 `C` 代表因果变换操作。

```lean
-- 规则组合
compose : C → C → C

-- 规则的输入和输出
input : C → List M
output : C → M
```

### 3. 因果偏序 (Causal Partial Order)
关系 `lt : M → M → Prop` 代表严格因果序。

```lean
-- 在 TestM 模型中
-- lt m0 m1 = True（m0 严格早于 m1）
```

### 4. 编织 (Weaving)
规则通过 `compose` 编织成复杂的因果网络。

---

## 公理体系

### AxiomA: 关系元与规则的存在性
```lean
class AxiomA (M C : Type*) where
  input : C → List M
  output : C → M
  input_nodup : ∀ α : C, (input α).Nodup
  compose : C → C → C
  compose_input : ∀ α β, input (compose α β) = input α ++ input β
  compose_output : ∀ α β, output (compose α β) = output β
  compose_assoc : ∀ α β γ, compose (compose α β) γ = compose α (compose β γ)
```

### AxiomB: 因果偏序 + 编织公理
```lean
class AxiomB (M C : Type*) [A : AxiomA M C] where
  le : M → M → Prop
  lt : M → M → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y
  lt_iff_le_not_le : ∀ x y, lt x y ↔ (le x y ∧ ¬ le y x)
  localFinite_past : ∀ x, Set.Finite {y | lt y x}
  localFinite_future : ∀ x, Set.Finite {y | lt x y}
  weaving_axiom : ∀ α x, x ∈ A.input α → lt x (A.output α)
```

### AxiomD: 操作编织的局部一致性（重构版）
```lean
class AxiomD (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  op_weaving : ∀ α β : C,
    B.lt (A.output α) (A.output β) →
    ∃ (γ : C), A.compose α γ = β
```

### AxiomC: 量子概率振幅
```lean
class AxiomC (M C : Type*) [A : AxiomA M C] where
  amplitude : C → ℂ
  norm_one : ∀ α, Complex.normSq (amplitude α) = 1
  comp_rule : ∀ α β, amplitude (A.compose α β) = amplitude α * amplitude β
  amplitude_injective : Function.Injective amplitude
```

---

## 实例化示例

### 示例 1: 最小反模型

在 [Core/AxiomD_Independence.lean](Core/AxiomD_Independence.lean) 中：

```lean
-- 关系元空间: M = {m0, m1}
inductive TestM | m0 | m1

-- 规则空间: C = {a, b, c}
inductive TestC | a | b | c

-- output 函数
-- a → m0, b → m1, c → m1
-- 因此 lt(output a)(output c) = lt(m0)(m1) = True

-- compose 函数设计使得 c 无法被生成
-- compose(_, a) = a, compose(_, b) = b, compose(_, c) = b
-- 因此不存在 γ 使得 compose(a, γ) = c
```

### 示例 2: 非平凡有限模型

在 [Core/Models/FinModels.lean](Core/Models/FinModels.lean) 中：

```lean
-- 使用 Fin 2 = {0, 1}
-- amplitude(n) = i^n (4次单位根)
-- 这满足 norm_one 和 comp_rule
-- 也是单射的（证明见 fin4_I_inj）
```

---

## 形式化示例

### 定义新模型

```lean
-- 在你的文件中
import Core.Axioms

-- 定义你的模型类型
inductive MyM | x | y
inductive MyC | r1 | r2

-- 实例化 AxiomA
instance : AxiomA MyM MyC where
  input := ...
  output := ...
  -- ... 其他字段

-- 实例化 AxiomB
instance [A : AxiomA MyM MyC] : AxiomB MyM MyC where
  le := ...
  lt := ...
  -- ... 其他字段
```

### 运行证明

```lean
theorem my_theorem
    [A : AxiomA MyM MyC]
    [B : AxiomB MyM MyC]
    (h : B.lt (A.output r1) (A.output r2)) :
    ∃ (γ : MyC), A.compose r1 γ = r2 :=
  by sorry
```

---

## 下一步

### 学习路径

1. **入门**: 阅读 [Core/Philosophy.lean](Core/Philosophy.lean) 理解 DSIO 哲学
2. **核心**: 研究 [Core/Theorems.lean](Core/Theorems.lean) 中的 `input_must_be_empty`
3. **独立性**: 阅读 [Core/AxiomD_Independence.lean](Core/AxiomD_Independence.lean) 学习反模型构造
4. **模型**: 查看 [Core/Models/FinModels.lean](Core/Models/FinModels.lean) 的非平凡实例

### 贡献指南

1. Fork 项目仓库
2. 创建新分支
3. 添加你的形式化工作
4. 确保编译通过 (`lake build`)
5. 提交 Pull Request

### 相关资源

- [Lean 4 文档](https://lean-lang.org/lean4/doc/)
- [Mathlib](https://leanprover-community.github.io/)
- [FutureWork/README.md](FutureWork/README.md) - 待研究的方向

---

**版本**: 10.5 | **状态**: 教科书典范级 | **编译**: Core 模块通过 ✅
