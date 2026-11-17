# Sp-8 一般 core 旗比較

## 所有と制約

- 新規葉 `SerrePositivity/KST/LocalizingInvariants/CoreFlag/` と独自 `All.lean`。
- `scripts/audit_kst_core_flag.lean` と本計画（300 行以下）。
- Sp 本体 d3・他レーンの既存ファイル・集約は編集しない。
- 新規 sorry / axiom / citation 禁止。ModelCategory SSet 不使用。
- 外部依存は既コミット公開モジュール。設計変更はユーザー経由で中継。

## 目標

任意の quasicategory C に対し

1. R(C)[m] = core Fun(Δ[m], C) を前合成で束ねる。
2. diag R(C) → C の対角評価 ε を構成し、C の後合成に関する自然性を示す。
3. ε の IsWeakHomotopyEquivalence を証明する。

## 方向の規約

外側の次数は旗、内側の次数は可逆な自然変換のパラメーター。
内部 Hom の評価の積は旗 × パラメーター。
定数包含はパラメーターを無視する（旗方向を保つ）。
課題文の「第二射影」はパラメーター × 旗という記法で読む。
行弱同値の適用時には二重単体集合を転置し、パラメーター次数を固定する。

転置した行は、Δ[m] の全辺を可逆辺に送る関手の部分圏と同定する。
core Fun の頂点は任意の旗であり、旗自体の辺を制限してはいけない。

## 採用経路

- a：定数包含 ι : C → diag R(C)、ι ≫ ε = id。
- b：転置後の各行に対する定数包含は圏同値。
  頂点 0 評価を逆とし、0 → i の辺を成分とする可逆自然変換で収縮する。
- c：行弱同値を anodyne 局所化可逆性へ渡し、
  `DiagonalLocalizedEquivalence.localized_diagonal_map` を適用する。
  転置による対角の同型も明示する。
- d：弱同値の 2-out-of-3 と ι ≫ ε = id。

## 作業

- [x] `functorDiagram`：標準単体の前合成を内部 Hom で束ねる。
- [x] `resolution` と要求された厳密な式の `diagonal`。
- [x] `counit`：二つの単体方向の恒等に代入する対角評価。
- [x] `map`、`diagonalMap`、`counit_naturality`：後合成と自然性。
- [x] 定数包含と切断恒等式。
- [x] 転置行の部分圏表示、頂点 0 評価と可逆収縮。
- [x] 圏同値から弱同値、anodyne 局所化との橋渡し。
- [x] ι と ε の弱同値。
- [x] 独自 All と型・公理監査。
- [x] 葉・All・audit の Lean 検証、禁止語・差分検査。

## 公開 API（検証後に確定）

名前空間 `SerrePositivity.KST.LocalizingInvariants.CoreFlag`。

- `resolution (C : SSet) : SimplexCategoryᵒᵖ ⥤ SSet`
- `diagonal (C : SSet) : SSet`
- `counit (C : SSet) : diagonal C ⟶ C`
- `map (f : C ⟶ D) : resolution C ⟶ resolution D`
- `diagonalMap (f : C ⟶ D) : diagonal C ⟶ diagonal D`
- `counit_naturality (f : C ⟶ D) : diagonalMap f ≫ counit D = counit C ≫ f`

K-cof への中継はユーザーが行う。他チャットへの直接送信は行わない。

## 証明と依存

- `rowIso` は二つの標準単体の変数交換であり、core 条件を
  `functorSimplex_isInvertible_iff` による点ごとの判定で移す。
- `constant_isQCatEquivalence` は任意の収縮を持つ始域について証明した。
  `Rows.lean` で標準単体の初頂点収縮に適用する。
- 弱同値と anodyne 局所化の橋渡しは既存の
  `EInfinity/Hammock/WeakAnodyneLocalization` と
  `EInfinity/FrameHom/AnodyneWeakDetection` にある。
- `DoubleSimplicialWeak.diagonalFunctor_map_weak` はこれらと
  `BisimplicialModel.localized_diagonal_map` を組み合わせた既存の公開定理。
- 最終定理は `WeakEquivalence.lean` の
  `inclusion_isWeakHomotopyEquivalence` と `counit_isWeakHomotopyEquivalence`。
- 一般の R(C) の行に対する頂点評価を自然変換として束ねる操作は使っていない。

## 検証

葉、独自 All、audit の `lake env lean` 検査に成功（2026-10-26）。
audit の推移的公理は `propext`・`Classical.choice`・`Quot.sound` のみと確認。
新規葉に禁止宣言なし。外部直接 import 5 件は全て HEAD と一致。
他レーンの既存ファイル・集約は編集していない。

## Sp-8 (2)：群 nerve の高次ホモトピー消滅

ユーザー採用の追加項目。所有範囲は CoreFlag の新規葉と独自集約・監査。

- [x] `KanHomotopy X n x` の n が実次数であることを確認。
- [x] `StrictSegalHomotopy.lean`：StrictSegal 性を使い、n > 1 なら
  境界定数 n 単体そのものが定数単体と一致することを証明。
  各 spine 辺は次元 1 なので境界内にあり、全辺定数から spine 単射性で回収する。
  これは提案された StrictSegal / coskeletal の経路の直接的な実装である。
- [x] 上記から StrictSegal な Kan 複体の `KanHomotopy` の一意性を証明。
- [x] `GroupNerveHomotopy.lean`：小さな亜群の nerve の Kan 性を
  ホモトピー圏と元の圏の同値から回収。
- [x] anodyne な連続 Kan 置換単位の既存の弱同値性を使用。
  そのホモトピー逆 r と既存の `kanPiIsomorphism_of_qCatEquivalence r` で、
  置換後の任意の基点 y の類を元の r(y) の類へ単射に写す。
  y が置換単位の頂点像であるという追加仮定は置かない。
- [x] 新規葉・独自集約・監査の Lean 検証成功。計 26 宣言の推移的公理は
  `propext`・`Classical.choice`・`Quot.sound` のみ。
  外部直接 import のプロジェクトモジュール 11 件は全て HEAD と一致。

公開名（名前空間は上記と同じ）：
`groupNerve_continuousKanReplacement_kanHomotopy_subsingleton`

型：任意の `(G : Type u) [Group G] (n : ℕ) (hn : 1 < n)` と
連続 Kan 置換された `nerve (AsSmall.{u} (SingleObj G))` の任意の頂点 x に対し、
`Subsingleton (Spectra.KanHomotopy (...) n x)`。

## 保存前の実施記録

- `set -o pipefail` の下で所有10モジュールを `lake env lean` で直列再検証（jobs=1）。
- 独自 audit は26宣言を検査し、エラー・警告なし。
- 推移的公理閉包は `propext`・`Classical.choice`・`Quot.sound` のみ。
- プロジェクト import 閉包は1548モジュール、うち所有外1538件は全てコミット済み・未変更。
- 保存対象は CoreFlag 全葉・All、独自 audit、本計画の12ファイルのみ。
