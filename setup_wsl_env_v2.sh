#!/bin/bash
# CSQIT WSL 编译环境配置脚本 v2
# 使用 Windows 本地的 elan 和 toolchain

echo "=========================================="
echo "CSQIT 10.4.5 WSL 编译环境配置"
echo "=========================================="

# 配置环境变量（使用 Windows 的 elan）
export ELAN_HOME=/mnt/c/Users/DELL/.elan
export PATH="$ELAN_HOME/bin:$PATH"

# 检查 elan
echo "[1/3] 检查 elan..."
if command -v elan &> /dev/null; then
    echo "  ✅ elan 版本: $(elan --version)"
elif [ -f "$ELAN_HOME/bin/elan.exe" ]; then
    echo "  ✅ 使用 Windows elan"
else
    echo "  ❌ elan 未找到"
    exit 1
fi

# 检查 lake
echo "[2/3] 检查 lake..."
if command -v lake &> /dev/null; then
    echo "  ✅ lake 版本: $(lake --version)"
elif [ -f "$ELAN_HOME/bin/lake.exe" ]; then
    echo "  ✅ 使用 Windows lake"
else
    echo "  ❌ lake 未找到"
    exit 1
fi

# 检查 mathlib
echo "[3/3] 检查 mathlib..."
if [ -d "/mnt/d/mathlib4/mathlib4-4.29.1" ]; then
    echo "  ✅ mathlib4 存在"
else
    echo "  ⚠️  mathlib4 不存在，需要复制"
fi

echo ""
echo "=========================================="
echo "配置完成！"
echo ""
echo "下一步："
echo "1. 如果需要复制 mathlib4："
echo "   cp -r /mnt/d/mathlib4 ~/.mathlib4"
echo ""
echo "2. 修改 lakefile 使用本地 mathlib："
echo "   复制 lakefile_wsl.lean 为 lakefile.lean"
echo ""
echo "3. 编译项目："
echo "   cd /mnt/d/CSQIT"
echo "   lake build"
echo "=========================================="
