# Mathlib へ上げる候補（補題単位、2026-10-29 新設）

概要：プロジェクトの補題のうち、Mathlib にない一般論で、単独で提出できる小さなものを一覧にする。
大きな塊（Auslander–Buchsbaum、Koszul、Cohen–Gabber など）は [paper-layer-extraction.md](paper-layer-extraction.md) の P1〜P9 で扱う。
方針：候補ごとに、最新の Mathlib で同じ主張がないことを確認した日付とコミットを記録する。提出の直前にもう一度確認する。
規約：提出するときは `SerrePositivity` 名前空間を外し、Mathlib の命名に合わせて改名する（ドット記法が使える名前空間へ）。
仮定は証明に必要な最小のものにしてから提出する。
使われ方：提出の順序と状態の管理。提出後は Mathlib の宣言名と PR 番号を書き、プロジェクト側は Mathlib 版へ置き換える。

## 1. 候補

| # | プロジェクトの宣言（所在） | 主張 | 提出時の名前と置き場所（案） | Mathlib の確認 | 状態 |
| --- | --- | --- | --- | --- | --- |
| U1 | `basis_mem_span_image_of_smul_mem`（LinearAlgebra/BasisSaturation） | 基底の部分集合の span は左非零因子による除算で飽和する。係数は非可換の半環でよく、`s ≠ univ` なら条件は必要でもある | `Module.Basis.mem_span_image_of_smul_mem`、LinearAlgebra/Basis/Basic.lean の `mem_span_image` の直後 | 8fe7ce4（2026-10-28）：なし。対になる事実 `LinearIndependent.eq_zero_of_smul_mem_span`、補部分加群 `LinearIndependent.isCompl_span_image` はある | 検討中（756143e99 で最小仮定に整理済み） |
| U2 | `basisOfRingEquiv`・`basisOfRingEquiv_apply`（LinearAlgebra/BasisRingEquiv） | 係数と元の両立する環同型の組に沿って基底を移す | `Module.Basis.mapRingEquiv`、LinearAlgebra/Basis/Basic.lean | 10-07 版：`Basis.map` と `Basis.mapCoeffs` の合成で書ける。単独の宣言はない | 優先度低（既存 API の合成） |
| U3 | `linearIndependent_of_smul_of_span_eq_top`・`basis_linearIndependent_smul_iff`（LinearAlgebra/BasisScalarIndependence） | `span R (range b) = ⊤` のとき、`b k • v i` の `R` 上独立から `v` の `S` 上独立。`b` が基底なら同値 | `LinearIndependent.of_smul_of_span_eq_top`・`Module.Basis.linearIndependent_smul_iff`、RingTheory/AlgebraTower.lean の `linearIndependent_smul` の直後（添字順は同補題に一致） | 8fe7ce4（2026-10-28）：順向きの `linearIndependent_smul` だけがある | 検討中（一般化と同値版を整備済み） |

## 2. 調査中
- `exists_linearIndependent_perturbation`（LinearAlgebra/IndependentPerturbation）：生成集合の元を足して独立にする。Mathlib にない（10-07 版）。

## 3. 候補ごとの調査メモ

- **U3**（2026-10-29、8fe7ce4）：順向き `linearIndependent_smul` は mathlib3 の `linear_independent_smul` の移植で、現在の Mathlib に利用箇所がない。
  塔の基底 `Module.Basis.smulTower` は 2024 年以前から `Basis.ofRepr`（座標の同型）で直接作られており、独立性の補題を経由しないため、逆向きが必要になる場面がなかった。
  張る側の対応物 `Submodule.span_smul_of_span_eq_top`（Algebra/Algebra/Tower.lean:394、仮定 `span R s = ⊤`）があり、U3 はその独立性版にあたる（名前と仮定の形を揃えた）。
  関連：`LinearIndependent.restrict_scalars`（係数の制限）、`LinearIndependent.algebraMap_comp_iff`、`linearIndependent_algebraMap_comp_iff`（係数拡大、整域）、
  `IntermediateField.LinearDisjoint.linearIndependent_left/right`・`of_basis_left`（線形分離：小さい体上の独立性が大きい体上でも保たれる条件）、
  `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable`（純非分離の塔での独立性の持ち上げ）。
