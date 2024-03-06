`adt-arr-heap` directory contains benchmarks encoded using the same named [SV-COMP benchmarks](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks) by [TriCera](https://github.com/uuverifiers/tricera). These benchmarks make use of the (currently non-standard) [theory of heaps](https://ceur-ws.org/Vol-3185/paper1180.pdf) for encoding heap. The files are appended by the checked property of its source file (e.g., `valid-memtrack`, `unreach-call`, etc.).

`adt-arr` directory contains benchmarks created using [heap2array](https://github.com/zafer-esen/heap2array) from the benchmarks in `adt-arr-heap` directory. In these benchmarks, all operations and sorts of the theory of heaps are encoded using the theories of arrays and ADTs.

Some files are appended by `-pp`, these benchmarks apply an experimental transformation to their base versions by introducing additional invariants.
