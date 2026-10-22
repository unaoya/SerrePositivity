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
  生成対象間の実際の `pinchedHomMap` の同値性まで。任意の Ind 対象間の充満忠実性と Ind 表現同値は未証明。
- 独立集約ビルド成功（7564 jobs）、公理監査 33 宣言で標準三公理のみ。主経路の ModelCategory・追加の同値性 instance なし。

### 残り（依存順）
1. accessible ∞ 圏：比較の全充満忠実性、Ind_κ(C₀) との同値・同値不変性、濃度変更（HTT 5.4.2〜5.4.4）。24〜60 時間（暫定）。
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

### 未コミット
- なし。工程 (1) の最初の検証済み区切りを所有ファイルのみ保存。

### 既知の問題
- 比較の充満忠実性は生成対象間だけ。全対象の同値性を追加の instance や構造のフィールドに仮定して完成扱いにしない。
- 工程 (2) の「Ind の presentable 性」は任意の小さい A に対しては成立しない。適切な小余極限の条件を明示して定理化する。

### 次の一手
- 工程 (1) の比較の充満忠実性。まず元の生成対象から任意の Ind 対象への写像空間比較を、
  単一 filtered 表示・両側の compact 性・同じ全余錐像の保存で証明する。
  次に始域の単一 filtered 表示と全反変 Hom の極限表示を使い、任意の二対象へ拡張する。
  F1 の関手圏の普遍性は、比較関手自身の同値性の代用にしない。

## 規約
- 配置 `SerrePositivity/InfinityCategories/F2/Presentable/`、集約 `F2/Presentable.lean`、監査 `scripts/audit_infinity_presentable.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。宇宙は F2/Ind の規約（Ind と標的は u+1、添字は u）に合わせる。
