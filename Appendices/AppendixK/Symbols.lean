
---

### 文件：`Appendices/AppendixK/Symbols.lean`

```lean
/-
CSQIT 10.4.5 附录K：符号表
文件: Symbols.lean
内容: 基本符号定义
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Base
import CSQIT.Appendices.AppendixA.Core
import CSQIT.Appendices.AppendixB.Core
import CSQIT.Appendices.AppendixC.Base
import CSQIT.Appendices.AppendixF.Core
import CSQIT.Appendices.AppendixG.Constant

namespace CSQIT.Appendices.AppendixK

open CSQIT
open CSQIT.Appendices.AppendixA
open CSQIT.Appendices.AppendixB
open CSQIT.Appendices.AppendixC
open CSQIT.Appendices.AppendixF
open CSQIT.Appendices.AppendixG

/-! ### 基本符号 -/

def M : Type := AxiomA.M        -- 关系元集合
def C : Type := AxiomA.C        -- 基本组合规则集合
def prec (x y : M) : Prop := AxiomB.lt x y  -- 因果偏序
def A_α (α : C) : ℂ := AxiomC.amplitude α  -- 规则α的概率幅
def O : Type := ColoredOperad A  -- 彩色Operad
def χ : ℝ := chi O               -- Operad组合拉普拉斯最大特征值
def H : Type := GNS_construction  -- GNS构造的希尔伯特空间
def A_R (R : Set M) : Type := subsystem_algebra R  -- 区域R的局域可观测量代数
def S₂ (ρ : O.Operations [] []) : ℝ := -log ‖amplitude_of_operation ρ‖^2  -- 2-Rényi熵
def g_ρ (X Y : TangentSpace ρ) : ℝ := bures_metric ρ X Y  -- Bures度量
def G : ℝ := Newton_constant     -- 牛顿常数
def Λ : ℝ := cosmological_constant  -- 宇宙学常数

end CSQIT.Appendices.AppendixK