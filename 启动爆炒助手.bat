@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo 正在启动爆炒江湖本地配队助手...
python app.py --port 8765
pause
