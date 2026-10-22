# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §2 の P、§6 の P。F1 の Ind_κ（F2/Ind）、N の冪等完備化と compact（F2/Idempotent、F2/Compact）、
> F1 の前層の極限・余極限、F1b の Kan 拡張と反射的局所化を読み取り専用で使う。第 I 段の到達点には不要で、第 II 段（BS-7 の animated 環、降下）の先行投資。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 (1) 進行中。κ-accessible を「正則 κ・小さい κ-filtered 余極限・小さい κ-compact 全部分生成圏」で定義。
  生成は各対象を厳密な頂点とする単一の全余錐表示。Ind との同値・比較の充満忠実性は定義に入れていない。
- 正則 κ の `IndInfinity κ A` の κ-accessibility を証明。F1 の単一 filtered 表示の同じ全余錐を Ind 内へ持ち上げ、N の Yoneda compact 性と合成。
- κ-accessible 関手は Ind の native な小さい κ-filtered 余極限保存を再利用。恒等・合成・濃度の単調性・全関手同型不変性を証明。
- 全 κ-compact 対象が生成対象の retract であることと、その逆を証明。元の生成族・対象を保持。
- 定義の小さい生成圏から κ-連続な Ind 比較を構成し、生成関手の全自然同型による回収・本質的全射性を証明。
  **元の任意の二対象間の `pinchedHomMap` の同値性・比較自身の全充満忠実性・全 ∞ 圏同値を証明。**
  `IsKappaAccessible.exists_indRepresentation` は定義の小さい compact 生成圏と κ-連続同値を回収。
  同値の順射は元の比較関手そのもの。`exists_indEquivalence` は小さい A の Indκ(A) との明示的な同値の存在。
- `covariantHomComparison` は任意の元の関手の全共変 Hom 比較。元の coslice 作用を厳密な底変換へ因子化し、
  left fibration の元の辺を straightening で送り、定義の全表現可能関手へ戻した関手圏の射。
  値ごとの同値族だけではない。指定評価成分の可逆性と元の `pinchedHomMap` の同値性の同値を証明。
  評価関手の始域を明記して型検査を軽くし、宇宙規約も保持。標的 coslice の回収同型は独立した定義。
- 実 coslice 比較の各 fiber を引き戻し fiber 同型で元の後合成へ厳密に回収し、同じ `pinchedHomMap` の同値性との同値を証明。
  `isFullyFaithful_iff_cosliceComparisonOver` は全始点での前合成同値性による全充満忠実性の判定。
  分類評価の全自然性と、実 fiber 評価が同じ `vertexFiberMap` の coherent 辺を回収する一単体の等式も証明。
  同じ Ind 比較の二つの生成対象で、元の実 coslice fiber 比較自身が同値であることまで接続。
- 全自然な関手圏の元の射について、両側が保存する同じ余極限の各項での可逆成分条件を、同じ頂点へ延長。
  元の射を表す一つの辺と全余錐を使用。両側の compact 性と厳密な宇宙持ち上げ・後合成式で小さい κ-filtered 版へ接続。
  `pinchedHomMap_equivalence_of_compact_colimit` を元の Ind の単一表示へ適用し、上記の生成対象から任意対象への実比較を得た。
- 極限側でも相対終対象の元の射影の充満忠実性から、同じ全比較の可逆成分条件を元の全錐の頂点へ延長。
  共変 Hom の極限保存、指定二対象の実比較の反転前後の同値性、元の余錐像の厳密な反転式を合成。
  `pinchedHomMap_equivalence_of_source_colimit` を Ind の始域の単一表示へ適用し、上記の全充満忠実性を得た。
- 独立集約ビルド成功（7599 jobs）、公理監査 91 宣言で標準三公理のみ。主経路の ModelCategory・追加の同値性 instance なし。

### 残り（依存順）
1. accessible ∞ 圏：同値不変性と Ind 表現による完全な iff、濃度変更・必要な基本性質（HTT 5.4.2〜5.4.4）。16〜40 時間（暫定）。
2. presentable の定義、前層 ∞ 圏・Ind_κ(C) の presentable 性（5.5.1.1、5.5.1.8）、局所小ささ。
3. presentable の小さい極限・余極限（5.5.2.4、5.5.3.13）。
4. 随伴関手定理：余極限を保つ関手は左随伴、accessible かつ極限を保つ関手は右随伴（5.5.2.9）。
5. Pr^L と Pr^R の双対性（5.5.3.4）。
6. Bousfield 局所化の存在（5.5.4.15）：N の `IsLocalObject`・`localEquivalences`・強飽和性・条件付き反射（HomotopyLimits）を再利用し、局所置換の存在を証明する。
7. P_Σ の普遍性と sifted 余極限による生成（5.5.8.14〜15）：N の `SigmaPresheafInfinity`・sifted 閉性・Yoneda の因子化を再利用する。

### 依存と提供
- 読み取り専用：`InfinityCategories/F2/Ind/`（F1）、`F2/Idempotent/`・`F2/Compact/`・`HomotopyLimits/`（N）、`F1/`（前層・Yoneda）、`F1B/`（Kan 拡張・局所化）、`Core/`。
- 提供先：第 II 段の BS-7（animated 環）、降下理論、K 第 II 段。

### 主要宣言
- `IsKappaAccessible`、`IsAccessible`、`IsKappaCompactGenerating`、`HasKappaFilteredGeneratorPresentation`
- `IsKappaAccessibleFunctor`、`IsAccessibleFunctor`、`indYoneda_isKappaCompactGenerating`、`indInfinity_isKappaAccessible`
- `IsKappaCompactGenerating.compact_iff_retract`、`IsKappaAccessible.exists_indComparison`
- `indComparison_isEssentiallySurjective`、`IsKappaAccessible.exists_surjective_indComparison`
- `indComparison_generator_pinchedHomMap_isEquivalence`
- `covariantHomComparison`、`cosliceComparisonOver`、`leftClassificationHom`
- `cosliceComparisonOver_fiber_postcomp`、`cosliceComparisonOver_fiber_equivalence_iff`
- `isFullyFaithful_iff_cosliceComparisonOver`、`indComparison_generator_cosliceFiber_isEquivalence`
- `leftClassificationEdge_evaluation_square`、`leftFibrationFiberEvaluation_original_edge`
- `covariantHomComparison_component_isIso_iff`、`functorHomComparison_colimit_vertex`
- `pinchedHomMap_equivalence_of_compact_colimit`、`indComparison_yoneda_pinchedHomMap_isEquivalence`
- `functorHomComparison_limit_vertex`、`pinchedHomMap_equivalence_iff_op`
- `pinchedHomMap_equivalence_of_source_colimit`、`indComparison_isFullyFaithful`、`indComparisonEquivalence`
- `IsKappaAccessible.exists_indRepresentation`、`IsKappaAccessible.exists_indEquivalence`

### 未コミット
- なし。工程 (1) の最初の検証済み区切りを所有ファイルのみ保存。

### 既知の問題
- accessible の同値不変性と、任意の指定 Ind 同値から accessibility を回収する逆方向は未証明。
- 工程 (2) の「Ind の presentable 性」は任意の小さい A に対しては成立しない。適切な小余極限の条件を明示して定理化する。

### 次の一手
- 工程 (1) の同値不変性。まず任意の元の全余錐の同値による保存・反映を、反転錐の既存の極限保存から証明。
  小さい κ-filtered 余極限の存在を同値で輸送する。元の `covariantHomComparison` は充満忠実な関手について
  全成分が可逆なので全関手同型を与える。その全比較と元の余錐像の式で compact 性を輸送する。
  同じ小さい生成圏・生成表示を輸送し、任意の Ind 同値から accessibility を回収して完全な iff を公開。
  続いて濃度変更と accessible 関手の必要な基本性質を進める。

## 規約
- 配置 `SerrePositivity/InfinityCategories/F2/Presentable/`、集約 `F2/Presentable.lean`、監査 `scripts/audit_infinity_presentable.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。宇宙は F2/Ind の規約（Ind と標的は u+1、添字は u）に合わせる。
