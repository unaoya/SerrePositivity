# ∞ 圏基盤の地図

quasicategory 模型を使う。∞ 圏は `X : SSet` と `[Quasicategory X]`、
関手は単体的集合の射、関手 ∞ 圏は `(ihom X).obj Y` で表す。
極限は slice の終対象、写像空間は右 pinched Hom として定義する。

## 層・入口・監査

ディレクトリ名の F1・F1B・F2 は開発レーンに由来する。入口の import と
監査の `#check` を目次として使う。作業状況は
[基盤計画](../../formalization-plans/foundations.md) と
[進捗](../../formalization-plans/foundations-progress.md) が正本。

| 層 | 内容 | 入口 | 監査（scripts/） |
| --- | --- | --- | --- |
| PinchedHom | 右 pinched 写像空間 | [PinchedHom/Basic.lean](PinchedHom/Basic.lean) | audit_infinity_core.lean |
| Core | join・slice、終対象、極限、同値、写像空間、fibration の基礎 | [Core.lean](Core.lean) | audit_infinity_core.lean |
| F1 | cocartesian fibration、straightening、Yoneda・前層 | [F1.lean](F1.lean)、[fibration の基本](F1/Fibrations.lean) | audit_infinity_f1.lean |
| F1B | Kan 拡張、随伴、cofinality、局所化 | [F1B.lean](F1B.lean) | audit_infinity_f1b.lean、audit_infinity_f1_f1b.lean |
| Coherent | coherent nerve の quasicategory 性（γ1） | [Coherent.lean](Coherent.lean) | audit_coherent_nerve.lean |
| DoldKanComparison | coherent nerve と dg nerve の比較（γ1.5） | [DoldKanComparison.lean](DoldKanComparison.lean) | audit_dold_kan_comparison.lean |
| HomotopyLimits | ホモトピー極限・Quillen 随伴の ∞ 圏比較（γ3・γ4） | [HomotopyLimits.lean](HomotopyLimits.lean) | audit_homotopy_limits.lean |
| F2 | Cat∞、filtered 余極限、Ind、compact、冪等完備化 | [F2.lean](F2.lean) | audit_infinity_f2.lean |
| Presentable | accessible・presentable、局所化 | [F2/Presentable.lean](F2/Presentable.lean) | audit_infinity_presentable.lean |
| Stable | 安定 ∞ 圏、cofiber、三角構造、完全関手 | [Stable.lean](Stable.lean) | audit_infinity_stable.lean |
| DGNerve | dg nerve、線形写像空間、h と H⁰ の比較 | [DGNerve.lean](DGNerve.lean) | audit_dg_nerve.lean |
| Derived | D(S)・Perf(S)、Verdier 商、dg 加群・Morita、gluing | [Derived.lean](Derived.lean) | audit_derived_infinity.lean |

監査はリポジトリ直下で `lake env lean scripts/<監査名>`、対象のビルドは
`lake build SerrePositivity.InfinityCategories.<入口名>` で行う。
主経路では `ModelCategory SSet` の instance 仮定を置かない。
公理監査は標準の `propext`・`Classical.choice`・`Quot.sound` のみを許す。

Core の基本入口は [Fibrations.lean](Core/Fibrations.lean) と
[MappingSpace.lean](Core/MappingSpace.lean)。辺の cocartesian 性と相対外側ホーンは
[F1/Fibrations.lean](F1/Fibrations.lean) にまとめる。

## 読み順と規約

[日本語解説の全体地図](../../exposition/ja/infinity/00-map.html) から、Core、F1・F1B、
γ 層、F2、Stable、dg nerve・Derived の順に読む。
[dg nerve の規約と計算](DGNerve/README.md) は移動前の符号・次数・N0 の計算を保存している。
微分は cochain 次数 +1、合成は通常順。HA と Kerodon の符号を比べる際はこの規約を参照する。

[リファクタリング計画](../../formalization-plans/refactoring-infinity.md) に従い、
移動した旧モジュールを削除し、下流の import と公開名を直接置換する。必要な補題が禁止 import 閉包にある場合は、
コピーせずコーディネータ経由で上流の分割を依頼する。
重複候補は `python3 scripts/check_duplicates.py --baseline
formalization-plans/archive/refactor-duplicates-2026-10-23.md` で比較できる。
