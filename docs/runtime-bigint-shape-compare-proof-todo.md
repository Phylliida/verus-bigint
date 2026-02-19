# Runtime BigInt Shape/Compare-Link Proof TODO

Proof goals that tie canonical limb shape to numeric range, and connect
comparison outcomes to truncated-subtraction behavior.

## Tight Length Characterization

- [x] Add nonzero value-window wrapper:
  - [x] `lemma_model_len_window_nonzero_ops(a)`
  - [x] prove `a != 0 ==> pow_base(len(a)-1) <= a < pow_base(len(a))`

- [x] Add zero-window characterization wrapper:
  - [x] `a == 0 ==> len(a) == 0`

## Compare/Sub Linkage

- [x] Add positive-compare subtraction wrapper:
  - [x] `lemma_cmp_pos_implies_sub_pos_ops(a, b) -> (cmp, sub_ab)`
  - [x] prove `cmp == 1 ==> sub_ab > 0`

- [x] Add equality-compare bidirectional subtraction wrapper:
  - [x] `lemma_cmp_eq_implies_bi_sub_zero_ops(a, b) -> (cmp, sub_ab, sub_ba)`
  - [x] prove `cmp == 0 ==> sub_ab == 0 && sub_ba == 0`

- [x] Add negative-compare asymmetric subtraction wrapper:
  - [x] `cmp == -1 ==> sub(a, b) == 0 && sub(b, a) > 0`
