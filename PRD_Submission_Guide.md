# CSQIT PRD 投稿材料清单与操作指南

**论文标题**：The Source Code of the Universe: Formal Deduction from Discrete Information to Cosmic Density  
**作者**：Zhang Jun (Jun Zhang)  
**期刊**：Physical Review D (PRD)  
**文章类型**：Regular Article  
**版本**：v11.2.0

---

## 一、投稿材料清单

### 1. 主论文文件

| 文件 | 说明 | 状态 |
|:---|:---|:---:|
| `CSQIT_SourceCodeOfUniverse_en_v11.2.0.tex` | LaTeX源文件（revtex4-2, aps,prd,twocolumn） | ✅ 已准备 |
| `references.bib` | BibTeX参考文献（8条） | ✅ 已准备 |

### 2. 投稿信（Cover Letter）

| 文件 | 说明 | 状态 |
|:---|:---|:---:|
| `Cover_Letter.md` | PRD投稿信（英文） | ✅ 已准备 |

### 3. 补充材料

| 文件 | 说明 | 状态 |
|:---|:---|:---:|
| `CSQIT_宇宙的源代码_zh_v11.2.0.md` | 中文版论文（供参考） | ✅ |
| `CSQIT_SourceCodeOfUniverse_en_v11.2.0.md` | 英文Markdown版（便于阅读） | ✅ |
| `CSQIT_宇宙的源代码_zh_v11.2.0.tex` | 中文LaTeX版（供参考） | ✅ |
| Lean 4 源代码 | 形式化证明代码（GitHub） | ✅ 已开源 |

### 4. 作者信息

| 字段 | 内容 |
|:---|:---|
| 作者姓名 | Zhang Jun (Jun Zhang) |
| 所属机构 | Independent Researcher |
| 通讯邮箱 | cnjun939@163.com |
| ORCID | 0009-0004-9803-3237 |

---

## 二、PRD 投稿操作步骤

### 步骤 1：准备投稿文件

1. 将以下文件复制到一个单独的投稿文件夹：
   - `CSQIT_SourceCodeOfUniverse_en_v11.2.0.tex`
   - `references.bib`
   - `Cover_Letter.md`（转成纯文本或PDF）

2. 确保LaTeX文件可以正常编译（本地测试）

### 步骤 2：访问 PRD 投稿系统

1. 网址：https://journals.aps.org/prd/
2. 点击 "Submit Manuscript"
3. 登录/注册 APS 账号（用 cnjun939@163.com）

### 步骤 3：填写投稿信息

**3.1 文章类型**
- 选择：Regular Article（不是 Letter）

**3.2 标题与摘要**
- Title: The Source Code of the Universe: Formal Deduction from Discrete Information to Cosmic Density
- Abstract: 使用LaTeX文件中的abstract内容

**3.3 作者信息**
- Author: Jun Zhang
- Affiliation: Independent Researcher
- Email: cnjun939@163.com
- ORCID: 0009-0004-9803-3237
- 设为通讯作者

**3.4 关键词（PACS / 分类）**
建议选择以下分类：
- 04.60.-m (Quantum gravity)
- 04.60.Gw (Quantum geometry and quantum topology)
- 03.67.-a (Quantum information)
- 98.80.-k (Cosmology)
- 02.10.Hh (Logic and set theory / theorem proving)

### 步骤 4：上传文件

1. 上传 LaTeX 源文件 (.tex)
2. 上传 BibTeX 文件 (.bib)
3. 上传 Cover Letter（粘贴到文本框或上传PDF）
4. 如有图片，逐一上传图片文件

### 步骤 5：选择编辑与审稿人

**建议编辑（可选）**：
- 如果有熟悉的编辑可以推荐
- 否则选择 "I don't have a preference"

**建议审稿人（可选）**：
- 可以推荐 3-5 位潜在审稿人
- 建议选择因果集理论、量子引力、形式化验证领域的专家

**排除审稿人（可选）**：
- 如有利益冲突的学者可排除

### 步骤 6：声明与确认

1. **利益冲突声明**：No conflicts of interest
2. **资金声明**：This work was conducted independently without external funding
3. **数据可用性**：The complete source code, formal proofs, and supplementary materials are publicly available at https://github.com/New-Beginning-Universe-Research-Group/CSQIT
4. **预印本**：如有 arXiv 预印本可填写编号
5. 确认所有作者同意投稿

### 步骤 7：提交

1. 预览确认所有信息无误
2. 点击 "Submit"
3. 保存投稿确认邮件

---

## 三、投稿信（Cover Letter）要点

Cover Letter 已包含以下核心亮点：

1. **零自由参数演绎链** — 从信息论公理出发，机器验证，无自由参数
2. **形式化验证** — Lean 4，50文件，~24,300行，2196编译任务，零错误
3. **经验锚点** — θ ≈ Ω_m（偏差~1%），与普朗克观测一致
4. **独特方法论** — 公理演绎驱动的形式化物理学，不同于弦论/圈量子引力/因果集
5. **受众** — 理论物理、数学物理、量子引力、基础物理研究者

---

## 四、论文亮点（审稿人关注重点）

| 亮点 | 说明 |
|:---|:---|
| 方法论创新 | 首次将Lean 4形式化验证用于完整的宇宙学公理体系 |
| 零自由参数 | θ=0.308完全由代数结构决定，无需调参 |
| 数值锚点 | 与普朗克2018观测值Ω_m=0.311偏差~1% |
| 唯一性论证 | 扩张谱系中只有p=7落在结构形成窗口 |
| 认识论框架 | W1/W2/W3三层分层，诚实标注确定性水平 |
| 存在性倒转 | 结构=7是观测者存在的必要条件 |
| 生长叙事 | 从公理种子到宇宙果实的有机生长框架 |

---

## 五、后续时间线

| 阶段 | 预期时间 | 说明 |
|:---|:---:|:---|
| 投稿 | Day 0 | 提交稿件 |
| 初审 | 1-2周 | 编辑决定是否送审 |
| 外审 | 1-3个月 | 2-3位审稿人评审 |
| 返修 | 1-2个月 | 根据审稿意见修改 |
| 接收 | — | 最终决定 |

---

## 六、备选方案

如果PRD审稿结果不理想，按以下顺序转投：

1. **Classical and Quantum Gravity (CQG)** — 专注引力物理，对离散引力友好
2. **Foundations of Physics** — 适合概念基础和方法论创新
3. **Annals of Physics** — 适合长篇系统性理论工作
4. **Physical Review Letters** — 如想试快报，可压缩后先投（被拒再转PRD）

APS同一系统内转投流程便捷，PRL被拒后可快速转PRD。

---

## 七、注意事项

1. **LaTeX编译**：投稿前确保本地编译无错，使用 `revtex4-2` 文档类
2. **参考文献**：BibTeX格式，使用 `\bibliography{references}`
3. **图表**：确保所有图表清晰，分辨率达标
4. **长度**：PRD Regular Article无严格长度限制，但建议30-40页以内
5. **补充材料**：Lean代码可作为补充材料或链接到GitHub
6. **ORCID**：确保已关联到投稿账号
7. **开源许可**：确认GitHub代码使用合适的开源协议（如MIT或Apache）

---

**准备状态**：✅ 所有材料已就绪，可随时投稿
