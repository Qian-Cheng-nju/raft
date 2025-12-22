#!/bin/bash
################################################################################
# 后台运行模型检验 - 简单包装脚本
################################################################################

cd /home/ubuntu/specula/data/repositories/raft/tla

echo "正在后台启动模型检验..."
echo "进程输出将保存到 nohup.out"
echo ""

nohup ./run_model_check.sh > nohup.out 2>&1 &

PID=$!
echo "✓ 模型检验已在后台启动！"
echo "  进程 ID: $PID"
echo ""
echo "常用命令："
echo "  查看实时日志:    tail -f nohup.out"
echo "  查看进程状态:    ps aux | grep $PID"
echo "  停止进程:        kill $PID"
echo "  强制停止:        kill -9 $PID"
echo ""
echo "日志文件位置: /home/ubuntu/specula/data/repositories/raft/tla/nohup.out"
