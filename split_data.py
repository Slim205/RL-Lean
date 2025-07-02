from datasets import Dataset, DatasetDict, load_dataset
import random


def split_by_file_and_push_to_hub(
    dataset: Dataset,
    hf_repo_name: str,
    train_size: float = 0.8,
    val_size: float = 0.1,
    test_size: float = 0.1,
    seed: int = 42,
    file_col: str = "file_name",
):
    """Split a hug'n'face :D dataset such that all rows from the same file stay together.

    The function groups the dataset by the value in ``file_col`` (default ``"file_name"``)
    and performs the train/validation/test split *at the file level* so that no file
    appears in more than one split.  The resulting :class:`~datasets.DatasetDict` is
    then pushed to the Hub.

    Args:
        dataset: Input :class:`~datasets.Dataset` containing a ``file_col`` column.
        hf_repo_name:  Destination Hub repo in the form ``"username/repo_name"``.
        train_size, val_size, test_size: Fractions that must sum to ``1.0``.
        seed: RNG seed for reproducibility.
        file_col: Name of the column that identifies the source file.
    """
    # Validate split fractions
    if not abs((train_size + val_size + test_size) - 1.0) < 1e-6:
        raise ValueError("train_size + val_size + test_size must equal 1.0")

    # Gather unique file identifiers and shuffle reproducibly
    unique_files = list(set(dataset[file_col]))
    random.Random(seed).shuffle(unique_files)

    # Determine split boundaries (integer rounding floors the counts)
    n_total = len(unique_files)
    n_train = int(n_total * train_size)
    n_val = int(n_total * val_size)

    # Assign files to splits
    train_files = set(unique_files[:n_train])
    val_files = set(unique_files[n_train:n_train + n_val])
    test_files = set(unique_files[n_train + n_val:])

    # Helper to filter rows belonging to a set of files
    def _belongs_to(ex, file_set):
        return ex[file_col] in file_set

    # Build the DatasetDict by filtering once per split
    split_data = DatasetDict({
        "train": dataset.filter(lambda ex: _belongs_to(ex, train_files)),
#        "validation": dataset.filter(lambda ex: _belongs_to(ex, val_files)),
        "test": dataset.filter(lambda ex: _belongs_to(ex, test_files)),
    })

    # Display basic statistics
    print(f"Dataset splits created (grouped by '{file_col}'):")
    for split_name, split_ds in split_data.items():
        n_rows = len(split_ds)
        n_files = len(set(split_ds[file_col]))
        print(f"- {split_name.capitalize()}: {n_rows} samples from {n_files} files")

    # Push to the Hub
    split_data.push_to_hub(hf_repo_name)
    print(f"\nDataset pushed to: https://huggingface.co/datasets/{hf_repo_name}")


if __name__ == "__main__":
    # Example usage
    dataset = load_dataset("Slim205/mathlib_bench_V1_2048", split="train")

    split_by_file_and_push_to_hub(
        dataset=dataset,
        hf_repo_name="Slim205/mathlib_RLjdjdj_v3",
        train_size=0.94,
        val_size=0,
        test_size=0.06,
        seed=42,
    )
