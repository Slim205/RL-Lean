import pyarrow.parquet as pq

dir_path = "/n/netscratch/amin_lab/Lab/slim/STP/storage/data/SFT/mathlib_leanworkbook_cache/mathlib_leanworkbook_json/"  #"/path/to/suspected/file.parquet"

for i in range(28) : 
    print(i)
    file_path = dir_path + f'chunk-{i}.parquet'
    try:
        table = pq.read_table(file_path)
        print(f"File {file_path} is OK. Rows: {len(table)}")
    except Exception as e:
        print(f"Error reading {file_path}: {str(e)}")