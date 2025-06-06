import os
import json
import pgzip
import logging
import pickle
import shutil
from typing import List, Any
#from google.cloud import storage
from multiprocessing import Pool
from functools import partial
import os
#logging.getLogger('google.auth').setLevel(logging.ERROR)
#logging.getLogger('urllib3.connectionpool').setLevel(logging.ERROR)

from os.path import expanduser
# HOME = expanduser("~")
# TPU_NAME = os.getenv('TPU_NAME')
# ZONE = os.getenv('ZONE')

ZIP_THREAD = 8

def _read_file(filename):
    compressed = filename.endswith('.gz')
    base_filename = filename[:-3] if compressed else filename
    
    if filename.startswith('gs://'):
        # Extract bucket name and path from the filename
        bucket_name, path = filename[len('gs://'):].split('/', 1)
        storage_client = storage.Client()
        bucket = storage_client.get_bucket(bucket_name)
        blob = bucket.get_blob(path)
        if blob is None:
            return None
        file_data = blob.download_as_string()
        if compressed:
            file_data = pgzip.decompress(file_data, thread=ZIP_THREAD)
        
    else:
        # Handle local file
        if not os.path.exists(filename):
            return None
        
        if compressed:
            file = pgzip.open(filename, 'rb', thread=ZIP_THREAD)
        else:
            file = open(filename, 'rb' if base_filename.endswith('.pkl') else 'r')
        file_data = file.read()
        
    if base_filename.endswith('.json'):
        return json.loads(file_data)
    elif base_filename.endswith('.jsonl'):
        spliter = '\n' if isinstance(file_data, str) else b'\n'
        return [json.loads(line) for line in file_data.split(spliter) if line]
    elif base_filename.endswith('.pkl'):
        return pickle.loads(file_data)
    else:
        return None

def read_file(filename):
    if filename is None:
        return None
    ret = _read_file(filename)
    if ret is None:
        ret = _read_file(filename + '.gz')
    return ret

def write_data(string, filename, content_type='json', no_compression=False):
    # This function writes serialized data to a file
    content_types = {
        'json': 'application/json',
        'jsonl': 'application/jsonl',
        'pickle': 'application/octet-stream',
    }
    if not no_compression:
        extension = '.gz'
        if isinstance(string, str):
            string = string.encode()
        string = pgzip.compress(string, thread=ZIP_THREAD)
    else:
        extension = ''
    full_filename = filename + extension

    if full_filename.startswith('gs://'):
        # Extract bucket name and path from the filename
        bucket_name, path = full_filename[len('gs://'):].split('/', 1)
        storage_client = storage.Client()
        bucket = storage_client.get_bucket(bucket_name)
        blob = bucket.blob(path)
        blob.upload_from_string(
            data=string,
            content_type=content_types.get(content_type, 'text/plain'),
        )
        result = f'{full_filename} upload complete'
    else:
        # Ensure directory exists
        os.makedirs(os.path.dirname(full_filename), exist_ok=True)
        # Handle local file
        with open(full_filename, 'wb' if (content_type == 'pickle') or (len(extension) > 0) else 'w') as file:
            file.write(string)
        result = f'{full_filename} write complete'
    logging.debug(result)

def move_file(source, target):
    if source.startswith('gs://') and target.startswith('gs://'):
        # Handle GCS to GCS move
        storage_client = storage.Client()
        source_bucket_name, source_path = source[len('gs://'):].split('/', 1)
        target_bucket_name, target_path = target[len('gs://'):].split('/', 1)
        
        source_bucket = storage_client.get_bucket(source_bucket_name)
        target_bucket = storage_client.get_bucket(target_bucket_name)
        
        source_blob = source_bucket.blob(source_path)
        
        # Copy the blob to the new location
        new_blob = source_bucket.copy_blob(source_blob, target_bucket, target_path)
        
        # Delete the original blob
        source_blob.delete()
        
        logging.debug(f"Moved {source} to {target} in GCS.")
        
    elif source.startswith('gs://') or target.startswith('gs://'):
        raise ValueError("Cannot move files between GCS and local filesystem directly.")
    else:
        # Handle local file move
        shutil.move(source, target)
        logging.debug(f"Moved {source} to {target} locally.")

def execute_on_all_workers(command, expect_succ = False):
    # Execute a command on all workers
    #compute_command = f'gcloud compute tpus tpu-vm ssh {TPU_NAME} --zone {ZONE} --worker=all --command "{command}"'
    exit_status = os.system(command)
    if expect_succ and (exit_status != 0):
        raise ValueError(f"Command failed with exit status {exit_status}")

def cleanup_dir(directory):
    # Cleanup a directory
    if directory.startswith('gs://'):
        command = f'gcloud storage rm -r {directory}'
        logging.debug(command)
        os.system(command)
    else:
        # Handle local directory
        shutil.rmtree(directory, ignore_errors=True)
        os.makedirs(directory, exist_ok=True)
        logging.debug(f"Deleted all files in {directory}")

def copy_dir(source, target):
    if source.startswith('gs://') or target.startswith('gs://'):
        command = f'gcloud storage cp -r {source} {target}'
        logging.debug(command)
        os.system(command)
    else:
        # Handle local directory copy
        shutil.copytree(source, target,dirs_exist_ok=True)
        logging.debug(f"Copied {source} to {target} locally.")

def path_exists(path):
    if path is None:
        return False
    if path.startswith('gs://'):
        # Handle GCS path
        storage_client = storage.Client()
        bucket_name, path_inside_bucket = path[len('gs://'):].split('/', 1)
        bucket = storage_client.get_bucket(bucket_name)
        blob = bucket.blob(path_inside_bucket)

        # Check if the blob exists
        if blob.exists():
            return True
        else:
            # Check if it's a directory by listing files with the given prefix
            blobs = list(bucket.list_blobs(prefix=path_inside_bucket + '/'))
            if blobs:
                return True
            return False
    else:
        # Handle local filesystem path
        return os.path.exists(path)