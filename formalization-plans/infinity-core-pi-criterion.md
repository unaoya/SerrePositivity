# Ind-π: coherent filtered 余錐の π 判定

開始: 2026-10-26 JST。停止条件: 二段目完了・設計変更提案・閉包破損・24時間。

## 所有と規約

- 新規葉 `SerrePositivity/InfinityCategories/F2/FilteredExchange/PiCriterion/`。
- 独自集約 `PiCriterion/All.lean`、`scripts/audit_f2_pi_criterion.lean`、本計画（≤300行）。
- 他レーンの葉・集約は編集しない。import は既コミット公開モジュールのみ。
- 新 sorry/axiom/citation なし。`ModelCategory SSet` 不使用。
- D の元ごとの条件の正確な型はユーザー経由で照会中（2026-10-26）。

## 目標

κ : Cardinal.{u}、κ-filtered poset I : Type u、w = max (u+1) v。
F : uliftFunctor.{w+1,u}.obj (nerve I) ⟶ SpaceInfinity.{w} と
c : JoinCocone F の native 余極限性を、全基点の KanHomotopyGroup の
filtered 余極限条件で判定する。正次数の添字 n は実際の次数 n+1。
空の空間を含めるため、π₀ の条件を省略しない。

## 実装順

1. 全空間の普遍余錐から c への指定比較と、その頂点での可逆性判定。
2. Kan 射の π₀・全基点正次数の Whitehead 判定。
3. 全空間への有限射の fiber 検出を、代表元と等式の有限段階検出へ接続。
4. 基点輸送と共通上界を保持し、D の指定する元ごとの条件を証明。
5. 宇宙分離、元の c への iff、集約と推移的公理監査。

## 確認した公開 API

- `coherentDiagramTotalCocone_isColimit`: 任意の小さい底に native 余極限。
- `nativeCoconeHomApex_isIso` と
  `isColimitCone_of_nativeCoconeHomApex_isIso`: 同じ余錐比較の頂点で判定。
- `coherentFilteredTotalKan_finite_value_detection`: 任意の有限 K の射は、
  ある値からの射とホモトピック。基点固定・段階間の等式は別途必要。
- `continuousKanReplacement_anchored_finite_factorization`: 元の境界を厳密に保持。
- `homotopyEquivalence_of_kanPiIsomorphism_of_piZero_surjective`: 空の場合も扱う。
- 上記の主要4定理の公理閉包は `propext, Classical.choice, Quot.sound` のみ。

## 宇宙と残課題

既存 coherent total API は底 SSet.{u} と SpaceInfinity.{u} が同じ宇宙。
最終型は底 u・値 w。ULift による底の移送と二重持ち上げ同型を先に検討する。
既存 API の複製が必要となれば R 候補としてここに記録する。
有限射の非相対検出だけから、指定基点での群の全射性・単射性はまだ結論しない。

## 検証

- 初期入力監査: `/tmp/audit-pi-inputs.lean`、4定理とも標準3公理のみ。
- 新規葉: 実装・ビルド中。
- 最終目標の達成は未宣言。
