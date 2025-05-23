import sys
from pathlib import Path
from typing import Dict, List, Tuple


def parse_information(information_file: Path) -> Tuple[id, str]:
    gpu_uuid = None
    minor = None
    with information_file.open(mode="r") as f:
        for line in f:
            split = line.split(":")
            if len(split) == 2:
                key, value = split
                if key == "Device Minor":
                    minor = int(value.strip())
                elif key == "GPU UUID":
                    gpu_uuid = value.strip()
    if gpu_uuid is not None and minor is not None:
        return minor, gpu_uuid
    else:
        raise ValueError(
            f"Could not parse information file {information_file.name}"
        )


def get_gpu_uuids() -> List[str]:
    gpus: List[str] = []
    if sys.platform.startswith("linux"):
        proc_folder = Path("/proc/driver/nvidia")
        gpus_folder = proc_folder / "gpus"
        capabilities_folder = proc_folder / "capabilities"

        id_mappings: Dict[int, str] = {}
        # First get all mappings from ID to UUID for physical GPUs
        if gpus_folder.is_dir():
            # Get all ID to UUID mappings
            for gpu_inf in gpus_folder.glob("**/information"):
                try:
                    gpu_id, gpu_uuid = parse_information(gpu_inf)
                except ValueError as e:
                    print(e)
                    continue
                id_mappings[gpu_id] = gpu_uuid

        # When capabilities folder exists, try to get MIG UUIDs
        if capabilities_folder.is_dir():
            # Loop capabilities to get (MIG) devices
            for gpu_cap in capabilities_folder.glob("gpu*"):
                gpu_id = int(gpu_cap.name[3:])
                gpu_uuid = id_mappings[gpu_id]
                # Check if this GPU is in MIG mode
                mig_devices: List[str] = []
                for gi in gpu_cap.glob("mig/gi*"):
                    gi_id = int(gi.name[2:])
                    for ci in gi.glob("ci*"):
                        ci_id = int(ci.name[2:])
                        mig_devices.append(f"MIG-{gpu_uuid}/{gi_id}/{ci_id}")
                if len(mig_devices) > 0:
                    # Device is in MIG mode, add MIG devices
                    gpus.extend(mig_devices)
                else:
                    # Device is not in MIG mode, add as regular GPU
                    gpus.append(gpu_uuid)
        # When capabilities folder does not exist, use physical GPUs
        else:
            gpus = list(id_mappings.values())

    else:
        print("Can currently only fetch GPU devices in linux")
    return gpus


if __name__ == "__main__":
    print(get_gpu_uuids())
