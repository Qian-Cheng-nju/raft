#!/bin/bash
################################################################################
# 模型检验配置脚本 - etcdraft_progress
# 修改下面的参数来控制模型检验行为
################################################################################

# ============================================================================
# 可配置参数 - 在这里修改！
# ============================================================================

MEMORY="2G"

# 线程数 (auto 自动检测, 或指定数字如 4, 8, 16)
WORKERS="auto"

# 超时时间（分钟），0 表示无限制
TIMEOUT_MINUTES=60

# 状态深度限制（0 表示无限制）
# 建议: 20-30 可以在合理时间内完成
MAX_DEPTH=25

# 是否启用对称性优化 (true/false)
# 注意：对称性可能导致某些错误被忽略，谨慎使用
ENABLE_SYMMETRY=false

# 检查点间隔（分钟）- 定期保存进度
CHECKPOINT_MINUTES=10

# 输出日志文件
LOG_FILE="mc_progress_$(date +%Y%m%d_%H%M%S).log"

# TLC 参数文件
SPEC_FILE="MCetcdraft_progress.tla"
CONFIG_FILE="MCetcdraft_progress.cfg"

# ============================================================================
# 以下为脚本逻辑，一般不需要修改
# ============================================================================

# 颜色输出
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}================================${NC}"
echo -e "${GREEN}模型检验启动配置${NC}"
echo -e "${GREEN}================================${NC}"
echo "内存限制:     $MEMORY"
echo "工作线程:     $WORKERS"
echo "超时时间:     $TIMEOUT_MINUTES 分钟"
echo "深度限制:     $MAX_DEPTH"
echo "对称性优化:   $ENABLE_SYMMETRY"
echo "检查点间隔:   $CHECKPOINT_MINUTES 分钟"
echo "日志文件:     $LOG_FILE"
echo -e "${GREEN}================================${NC}"

# 构建 TLC 命令
TLC_CMD="java -XX:+UseParallelGC -Xmx${MEMORY} -Xms${MEMORY}"
TLC_CMD="$TLC_CMD -cp ../../../../lib/tla2tools.jar:../../../../lib/CommunityModules-deps.jar"
TLC_CMD="$TLC_CMD tlc2.TLC"

# 添加工作线程
TLC_CMD="$TLC_CMD -workers $WORKERS"

# 添加检查点
if [ $CHECKPOINT_MINUTES -gt 0 ]; then
    TLC_CMD="$TLC_CMD -checkpoint $CHECKPOINT_MINUTES"
fi

# 添加深度限制
if [ $MAX_DEPTH -gt 0 ]; then
    TLC_CMD="$TLC_CMD -depth $MAX_DEPTH"
fi

# 添加超时
if [ $TIMEOUT_MINUTES -gt 0 ]; then
    TIMEOUT_SECONDS=$((TIMEOUT_MINUTES * 60))
    TLC_CMD="timeout ${TIMEOUT_SECONDS}s $TLC_CMD"
fi

# 添加配置和规范文件
TLC_CMD="$TLC_CMD -config $CONFIG_FILE $SPEC_FILE"

echo -e "${YELLOW}执行命令:${NC}"
echo "$TLC_CMD"
echo ""
echo -e "${GREEN}开始模型检验...${NC}"
echo ""

# 执行命令并记录日志
eval $TLC_CMD 2>&1 | tee $LOG_FILE

# 检查退出状态
EXIT_CODE=${PIPESTATUS[0]}

echo ""
echo -e "${GREEN}================================${NC}"
if [ $EXIT_CODE -eq 0 ]; then
    echo -e "${GREEN}✓ 模型检验完成，未发现错误${NC}"
elif [ $EXIT_CODE -eq 124 ]; then
    echo -e "${YELLOW}⚠ 模型检验超时${NC}"
elif [ $EXIT_CODE -eq 12 ]; then
    echo -e "${YELLOW}⚠ 发现不变式违反！${NC}"
    echo -e "${YELLOW}请查看日志: $LOG_FILE${NC}"
else
    echo -e "${YELLOW}⚠ 模型检验异常退出 (退出码: $EXIT_CODE)${NC}"
fi
echo -e "${GREEN}================================${NC}"

exit $EXIT_CODE
