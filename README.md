# Rule 30 research checkpoint

The immutable Lean target and audit are in `immutable/`. The shared, **incomplete** working Lean proof is `step4/Solution.lean`. It still has a `sorry`; this is a research checkpoint, not a solution. Lean is pinned to 4.35.0.

## Restore the initial workspace snapshot

The snapshot includes the project sources, both workers' proof notes, replay code, logs, and project-generated Lean caches, including `immutable/.lake/build`. It does not include an installed public Lean distribution or unrelated workspace data. Extract into a new directory:

```sh
mkdir r30-restored
cat checkpoints/initial/project.tar.zst.part-* > r30-restored/project.tar.zst
cd r30-restored
printf '%s  project.tar.zst\n' '2de6460c95fcf675d21b217cdd80b2212e680aad9f9ecfbf7ef989fb8e11ae4b' | sha256sum -c -
tar --zstd -xf project.tar.zst
```

Shards are a byte-for-byte split of one zstd archive, not individual archives. Later worker syncs are tracked separately as incremental files under the worker directories; use the newest committed files for ongoing work.
