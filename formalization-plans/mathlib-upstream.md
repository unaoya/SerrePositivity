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
| U4 | `exists_add_notMem_of_span_eq_top`・`exists_linearIndependent_add_of_span_eq_top`（LinearAlgebra/IndependentPerturbation） | 生成集合 `W` の元か 0 を足して真部分加群を避ける（任意の環上の加群）。有限個の族は、個数が階数以下なら `W ∪ {0}` の元を足して独立にできる（除法環、無限次元・有限体を含む） | `Submodule.exists_add_notMem_of_span_eq_top`・`exists_linearIndependent_add_of_span_eq_top`、LinearAlgebra/Dimension/RankNullity.lean の `exists_linearIndependent_cons_of_lt_rank` の近く | 8fe7ce4（2026-10-28）：なし。足す元に制約のない延長 `exists_linearIndependent_cons_of_lt_rank`、存在 `exists_linearIndependent_of_le_rank`、大きな体での回避 `Submodule.exists_forall_notMem_of_forall_ne_top` はある | 検討中（一般化・改名済み） |
| U5 | `adjoinSingletonDerivation`・`exists_derivation_extension_iff`・`adjoinSingletonObstruction`（FieldTheory/AdjoinSingletonDerivation） | 体 `K` 上で一元 `x` が生成する可換環 `L` で、導分 `δ : K → V` を `x ↦ v` と延長できることと、最小多項式 `f` について `f^δ(x) + f'(x) • v = 0` は同値。延長はデータとして構成。`x` が整である仮定は不要 | `Derivation.extendAdjoinSingleton`・`Derivation.exists_extend_adjoin_singleton_iff` など、RingTheory/Derivation/MapCoeffs.lean の `apply_aeval_eq'` の近く。`f^δ(x)` は Mathlib の `PolynomialModule.eval x (map _ (δ.mapCoeffs f))` で書く | 8fe7ce4（2026-10-28）：なし。微分体の分離的な場合の構成（FieldTheory/Differential/Basic.lean、`AdjoinRoot` 上で `implicitDeriv`）、必要性に使う評価公式 `Derivation.apply_aeval_eq'`、核に沿った持ち上げ `Derivation.liftOfSurjective`（終域が環自身の場合のみ）はある | 検討中（一般化済み。降下 `descendModuleDerivation` の Mathlib 化と合わせて提出） |
| U6 | `ker_mapBaseChange_of_adjoin_singleton`・`kaehlerDifferentialBasisOfAdjoinSingleton`・`finrank_kaehlerDifferential_eq_of_adjoin_singleton`（FieldTheory/AdjoinSingletonDifferential） | 体 `K` 上で一元 `x` が体 `L` を生成し最小多項式 `f` の微分が零のとき、`Ω_{L/K}` は `D x` を基底とする1次元で、`ker (L ⊗_K Ω_{K/R} → Ω_{L/R})` は `f^D(x) = Σ xⁱ ⊗ D(fᵢ)` の張る直線。それが零でなければ `dim Ω_{L/R} = dim Ω_{K/R}` | RingTheory/Kaehler の第一基本完全列（`mapBaseChange`・`exact_mapBaseChange_map`）の近く。U5 と組で提出 | 8fe7ce4（2026-10-28）：なし。完全列 `exact_mapBaseChange_map`・`range_mapBaseChange`、エタールの場合の同型 `tensorKaehlerEquivOfFormallyEtale` はある | 検討中（U5 に依存） |
| U7 | `exists_maximal_intermediateField_not_mem`（FieldTheory/ExponentOneDifferentialConstants） | 有限次拡大 `K/F` と底体の外の元 `x` について、`x` を含まない中間体のうち極大なものがある（拡大次数の最小化で選ぶ） | `IntermediateField.exists_maximal_notMem`、FieldTheory/IntermediateField の有限次元の節 | 8fe7ce4（2026-10-28）：なし | 検討中 |

## 2. 調査中
（なし）

## 3. 候補ごとの調査メモ

- **U3**（2026-10-29、8fe7ce4）：順向き `linearIndependent_smul` は mathlib3 の `linear_independent_smul` の移植で、現在の Mathlib に利用箇所がない。
  塔の基底 `Module.Basis.smulTower` は 2024 年以前から `Basis.ofRepr`（座標の同型）で直接作られており、独立性の補題を経由しないため、逆向きが必要になる場面がなかった。
  張る側の対応物 `Submodule.span_smul_of_span_eq_top`（Algebra/Algebra/Tower.lean:394、仮定 `span R s = ⊤`）があり、U3 はその独立性版にあたる（名前と仮定の形を揃えた）。
  関連：`LinearIndependent.restrict_scalars`（係数の制限）、`LinearIndependent.algebraMap_comp_iff`、`linearIndependent_algebraMap_comp_iff`（係数拡大、整域）、
  `IntermediateField.LinearDisjoint.linearIndependent_left/right`・`of_basis_left`（線形分離：小さい体上の独立性が大きい体上でも保たれる条件）、
  `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable`（純非分離の塔での独立性の持ち上げ）。
