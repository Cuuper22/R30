# Checkpoint workflow

The two workers independently checkpoint their own files on a roughly 15-minute cadence and at substantive results. Each incremental commit uses the current `main` as its parent and then fast-forwards `main` without force. A competing commit causes a rebuild from the latest `main`, preserving the other worker’s changes. The runner uses the existing GitHub connector and does not store a credential.

For restoration, extract the initial archive first and overlay the latest tracked `immutable/`, `step4/`, `ancestry_ultra/`, `bounds_ultra/`, and `runtime-evidence/` files from the Git checkout. The original `.gitignore` is empty. Commits do not claim that the incomplete proof passes the final audit.
