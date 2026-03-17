/-
CSQIT 10.4.5 附录H：统一导出
文件: Export.lean
内容: 导出所有核心定义和定理
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixH.Core
import CSQIT.Appendices.AppendixH.EntropyArea
import CSQIT.Appendices.AppendixH.Information

namespace CSQIT.Appendices.AppendixH

-- 导出核心定义
export CSQIT.Appendices.AppendixH (BlackHoleRegion)
export CSQIT.Appendices.AppendixH (boundary_area)
export CSQIT.Appendices.AppendixH (gamma)

-- 导出核心定理
export CSQIT.Appendices.AppendixH (horizon_weaving_structure)
export CSQIT.Appendices.AppendixH (entropy_area_relation)
export CSQIT.Appendices.AppendixH (information_conservation_during_evaporation)
export CSQIT.Appendices.AppendixH (information_paradox_resolution)

end CSQIT.Appendices.AppendixH