# CSQIT 项目有效工作流

**版本**: v11.6.0 | **日期**: 2026-07-13 | **Lean**: v4.29.0-rc6

---

## 1. 工作目录结构

### 1.1 WSL (Linux) 端

```
/home/dell/
├── CSQIT_Refactor/          [主工作目录 - 新结构 W1/W2/W3]
│   ├── Core/
│   │   ├── W1/              [形式化数学核心]
│   │   ├── W2/              [连续极限与物理应用]
│   │   └── W3/              [探索性框架]
│   ├── Unified/             [统一常数与模型]
│   ├── Appendices/          [附录]
│   ├── .lake/
│   │   └── packages -> ~/lean_deps/.lake/packages  [符号链接]
│   └── lakefile.lean
│
├── CSQIT_Project/           [旧结构 - 仅作参考]
│   └── .git -> D:/CSQIT-workspace/.git/worktrees/...
│
└── lean_deps/               [全局依赖目录]
    └── .lake/packages/      [mathlib 3032 olean文件]
```

### 1.2 Windows 端

```
D:\n├── CSQIT-workspace-refactor/  [Windows同步副本]
│   ├── Core/W1/W2/W3/
│   ├── Unified/
│   └── Appendices/
│
└── CSQIT-workspace/           [旧结构 - Trae IDE workspace]
```

---

## 2. 编译环境

### 2.1 工具链
- Lean: `leanprover/lean4:v4.29.0-rc6`
- Lake: `5.0.0-src+00659f8`
- elan: 已安装

### 2.2 依赖管理
- mathlib 缓存位于 `~/lean_deps/.lake/packages/mathlib/.lake/build/`
- 共 3032 个 olean 文件
- 通过符号链接共享给所有项目

### 2.3 编译命令
```bash
cd ~/CSQIT_Refactor

# 完整编译
lake build

# 编译特定模块
lake build Core.W1.WeavingStructure
lake build Core.W2.ContinuumLimit

# 获取缓存（如需要）
lake exe cache get
```

### 2.4 内存配置（WSL）
在 `.wslconfig` 中设置：
```ini
[wsl2]
memory=6GB
swap=8GB
```

---

## 3. rsync 同步流程

### 3.1 WSL -> Windows
```bash
cd ~/CSQIT_Refactor
rsync -av --delete \
  --exclude=".lake" \
  --exclude="*.py" \
  --exclude="*.log" \
  --exclude="Test*.lean" \
  --exclude="test*.lean" \
  --exclude="*.bak*" \
  --exclude="all_lean_*" \
  ./ /mnt/d/CSQIT-workspace-refactor/
```

### 3.2 Windows -> WSL（初始同步）
```bash
rsync -av --delete \
  --exclude=".lake" \
  --exclude="*.log" \
  /mnt/d/CSQIT-workspace-refactor/ ~/CSQIT_Refactor/
```

---

## 4. Git 工作流

### 4.1 当前分支
- 工作分支: `feat-continue-optimization`
- 基于分支: `feat-create-new-branch-f8frBB`
- 远程: `origin/feat-create-new-branch-f8frBB`

### 4.2 提交规范
```bash
cd ~/CSQIT_Refactor
git add -A
git commit -m "description"
git push origin feat-continue-optimization
```

### 4.3 常用命令
```bash
# 查看修改状态
git status

# 查看修改内容
git diff

# 创建新分支
git checkout -b feat-new-feature

# 推送新分支
git push -u origin feat-new-feature
```

---

## 5. 文件修改记录

### 5.1 本次修改的文件
| 文件 | 修改内容 |
|------|----------|
| Core/W1/Consistency.lean | 修复第310行sorry（lt_irrefl定理） |
| Core/W1/WeavingStructure.lean | 修复示例路径、comp函数h_last、保留h_cc为sorry |
| Core/W1/AxiomC_Independence.lean | import路径修复：Core.Theorems -> Core.W1.CausalWeaving |
| Core/W1/AxiomD_Independence.lean | import路径修复 |
| Core/W1/Unified.lean | import路径修复 |
| Appendices/AppendixA-E/*.lean | import路径修复（5个文件） |
| PROJECT_STATUS.md | 更新版本号和编译状态 |

---

## 6. 编译状态

### 6.1 当前状态
- **编译结果**: 通过（3331 jobs）
- **错误数**: 0
- **Warning**: 仅 linter 代码风格提示
- **sorry数**: 10（含4个有意保留）

### 6.2 编译历史
- 2026-07-13: 首次完整编译通过（3331 jobs）
- 2026-07-13: 修复9个import路径后再次编译通过

---

## 7. 常见问题

### Q1: mathlib缓存下载失败
**解决**: 使用符号链接共享 `~/lean_deps/.lake/packages`

### Q2: Core.Theorems模块不存在
**解决**: 替换为 `Core.W1.CausalWeaving`

### Q3: WSL内存不足
**解决**: 调整 `.wslconfig` memory=6GB, swap=8GB

### Q4: 两个编译进程冲突
**解决**: 确保同一时间只有一个 `lake build` 在运行

---

## 8. 项目信息

- **维护者**: DELL
- **项目**: CSQIT（因果结构量子信息理论）
- **GitHub**: New-Beginning-Universe-Research-Group/CSQIT
