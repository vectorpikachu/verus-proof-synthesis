import csv
from pathlib import Path
import subprocess

import pandas as pd

# 设置路径
benchmark_root = Path("../benchmarks")
csv_path = Path("new_result.csv")  # 可自定义

def row_exists(csv_path, name):
    try:
        df = pd.read_csv(csv_path)
        return name in df['name'].values
    except FileNotFoundError:
        return False

# 创建并打开 CSV 文件，准备写入 header 和每个未验证文件的路径
with open(csv_path, mode="a", newline="") as csvfile:
    writer = csv.writer(csvfile)
    writer.writerow(["name", "has_proof_function"])  # 写入表头

    # 遍历符合条件的 rs 文件
    for dir1 in benchmark_root.iterdir():
        unverified_dir = dir1 / "unverified"
        if not unverified_dir.exists():
            continue

        for rs_file in unverified_dir.glob("*.rs"):
            rs_path_str = str(rs_file.resolve())

            # 写入路径和初始的 False
            writer.writerow([rs_path_str, False])

            # 运行对应的命令（你也可以注释掉这行，只生成 CSV）
            subprocess.run([
                "uv", "run", "main.py",
                "--input", rs_path_str,
                "--output", rs_path_str + "-out.rs",
                "--config", "config.json"
            ])
