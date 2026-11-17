# Verdier 商の一般構成に向けたリファクタ計画（2026-10-28 新設、調査のみ・コード変更なし）

概要：安定 ∞ 圏の Verdier 商を一般に構成することを当面の目標とし、その前段として、Verdier 列・局所化・分数・
冪等完備化の一般論を KST と Derived から ∞ 圏の層（`InfinityCategories/Stable`、`F1B/Localization`）へ集め、
定義の二重化を解消する計画。新しい数学（商の存在など）は §5 に分けて記し、本計画の移動とは混ぜない。
方針：[R 第 2 窓](refactoring-infinity-r2.md) と同じ運用。全レーン停止窓で `scripts/move_module.py`
（モジュールの移動と import の書き換え。宣言の名前空間は変えない）と `scripts/refactor/verify.sh` で実施する。
公開名・型・数学的内容は保存する。候補は R2 の続き番号 R48〜 とし、R45（LocalizingInvariants の一般部分を下位へ）を細分化したものとして扱う。
規約：各候補に「対象・移動先・影響する利用元・前提・検証・工数」を書く。調査値は HEAD `cbb891432` 時点。
使われ方：R 第 2 窓の実施順を決めるときに R2 §3〜§4 と合わせて読む。所有の変更（§1.3）はコーディネータが決める。

> 注（10-28）：層の名前・段・前提・規模・工数は [infinity-foundation-plan.md](infinity-foundation-plan.md) が正本。本書の値は調査時点の記録で、同書のレビューで再計測・修正されたものがある（例：R56・R49・R50・R37・R54・R65）。

## 1. 現状（調査結果の要約）

### 1.1 Verdier 列の定義は二つあり、互いの関係を示す補題がない

| | `IsVerdierSequence` | `IsStableVerdierSequence` |
| --- | --- | --- |
| 場所 | KST/LocalizingInvariants/VerdierSequence.lean | InfinityCategories/Derived/StableVerdierSequence.lean（26 行） |
| 形 | 束ねた形：`StableCategory`・`ExactMap` | 束ねない形：`SSet` と `[Quasicategory]`・`[IsStable]` のインスタンス |
| 核の条件 | `q b ≃ 0 ↔ b ∈ essentialImage i`（核と像が一致し、像は厚い） | `kills` のみ（i の像が q で 0 に行く） |
| 商の条件 | `IsLocalization q (cofiberLocalizingEdges (essentialImage i))`。すべての quasicategory に対する DK 局所化 | `zeroingExactPrecomposition` が同値。安定な行き先と完全関手だけに対する普遍性 |
| 利用 | Fibration 134・SConstruction 6・NonConnective 2 ファイル。ほとんどが仮定 `(h : IsVerdierSequence i q)` とフィールドの射影 | Derived 5・NonConnective 2 ファイル。すべて dg の具体例 |
| 結論とする定理 | 随伴による判定 `isVerdierSequence_of_adjoint`、半直交分解、Tamme の lax 系、dg の Milnor／κ 系 | dg 商（Drinfeld、resolved）、gluing、`dgKappaSuspension_isStableVerdierSequence` |

前者は 9 人論文 II.A.1 の Verdier 列にあたる（核を厚い部分圏として持つ）。後者は「完全関手として普遍的な商」で、条件がより弱い。

### 1.2 一般論が置かれている場所

- **KST/LocalizingInvariants（2007 ファイル）**：K・BF・dg を含まないファイルは 514 本（コード上）。import の閉包まで含めて K・BF・dg を含まないものは 342 本。
  - 基礎ブロック 7 本：`StableCategories`・`ExactEnrichment`・`StableInfinity`・`VerdierSequence`・`AdjointLocalization`・`AdjointVerdier`・`VerdierDiagrams`。
    閉包に含まれる KST のモジュールはこの 7 本だけなので、そのまま ∞ 層へ移せる。`Invariant`（`IsLocalizingInvariant`）は Sp が必要なので KST に残る。
  - 分数・Ore・span の機構 `Verdier*` は 93 本ある。コード上はすべて一般論だが、閉包まで含めて一般なのは 6 本だけで、残りは次の三つの経路で KST に依存している。
    (a) `StableCospanPullbacks` → `KST.SConstruction.StableSpanPushout`（中身は一般の安定 span pushout）。
    (b) `KST.Fibration.RelativeFirstRowSimplexQuotient`（`Φ : StableInfinity ⟶ Sp` を使う）。
    (c) `Tamme*`・`Lax*` と HomotopyLimits を経由する経路（HL → KST.Spectra は R27 の対象）。
  - そのほかの一般論の群：Cofiber* 29、Localization* 11、Arrow* 18、Square* 17、Marked* 11、Composition* 9、Completion* 8、Exact* 8、Reflective* 5 など（一般論で、閉包もほぼ一般）。
    Lax* 84 と Tamme* 27 は一般の数学だが、Sp に値をとる系と混ざっている。
  - LocalizingInvariants と KST/Fibration は互いに import し合っている（`Fibration/WeakEquivalences`・`GroupoidCompletion*` を Verdier* が使う）。
- **InfinityCategories/Derived**：dg を含まないモジュールは 4153 本中 185 本。商に関係するものは次のとおり。
  - `ExactFunctorCategory`・`ExactFunctorCategoryEquivalence`・`ExactFunctorDescent`・`StableVerdierSequence`。閉包に KST・dg を含まない。
  - `RestrictedDeformationLocalization`（局所化の一般判定）。
  - `ActualRoof*`・`Roof*`・`WeakRoof*`（屋根による分数）。
- **Stable**：`CofiberLocalizingEdges`・`CofiberLocalizing{BaseChange,Composition}`、`StableVertexClosure`・`StableHoClosure`、
  `CofiberHoDenominators`（ホモトピー圏での分数計算：二つのうち三つ、共通分母、有限個の等化）、`ExactFunctorKernelEdges`、`IdempotentCompletionDensity`。
- **F1B/Localization**：`IsLocalization` とその普遍性、saturation、判定法（deformation 系・右 Kan 系）、`exists_small_inverting_factorization`。
  F1B 自身は、任意の W に対する局所化の存在を主張していない（docstring に明記）。
  **訂正（10-28 夕）**：存在の定理は KST にある。`exists_quasicategory_localization (X : SSet) (W) : ∃ Q F, Quasicategory Q ∧ IsLocalization F W`
  （KST/LocalizingInvariants/LocalizationResolution.lean:37。逆辺の貼り付けと inner anodyne 置換による）。
  `GeneralLocalization.lean` で `edgeLocalization` としてまとめられている。関係するファイルは約 40 本で、閉包に dg は入っていない。
  詳しくは [外部調査](../infinity-outside-survey-2026-10-28.md) の L4 を参照。
- **F2**：Ind（`ind_isStable_unconditional`、compact ≃ `Idem`）、Bousfield 局所化（`bousfieldLocalizationFunctor_isLocalization_generatedEdges`）、
  冪等完備化（`IsIdempotentCompletion.isStable`・`.isExactFunctor`）、`retractClosure`。F2/Presentable には `IsStable` も `IsExactFunctor` も出てこない。
- **厚い部分圏**：一般の述語はなく、dg 版 `dgThickClosureProperty`（Derived/DGQuotientThickKernelCriterion）だけがある。Karoubi 列の定義もない。

### 1.3 所有と既存計画

- foundations-progress:235 では、局所化・分数・Verdier 商の API の正本は Sp（KST/Spectra・KST/LocalizingInvariants）の所有となっている。
  ∞ 層へ移すと所有も移る。**10-28 ユーザー決定：∞ 層へ移す**（新しい持ち主は R 第 2 窓の割り当てで決める）。
- R45（LocalizingInvariants 24 辺の一般部分を下位へ）、R27（HL → KST.Spectra）、R31（PiCriterion の配置）、R37・R38（Stable と F2 の層）、
  R40（`Stable.Base < F2 < Stable.F2Applications` の層規約）が本計画と重なる。本計画はこれらと矛盾しないように番号を振る。

## 2. 目標とする配置

```
F1B/Localization/            IsLocalization（既存）＋ AdjointLocalization・RestrictedDeformationLocalization
Stable/Exact/                exactFunctors・zeroingExactPrecomposition・ExactFunctorDescent（Derived から）
Stable/Verdier/              Basic（束ねない正本の定義）・Bundled（StableCategory／ExactMap／VerdierSequence）
                             Adjoint（随伴による判定）・Thick（厚い部分圏）・Comparison（二つの定義の比較）
Stable/Verdier/Fractions/    LI の Verdier* 分数機構・ActualRoof*／Roof*・CofiberHoDenominators の上位部分
Stable/Infinity/             StableCategory を対象とする ∞ 圏 StableInfinity・VerdierDiagram（Cat^ex_∞）
StablePresentable/           （新しい数学の置き場、§0.2 の名前に合わせた）Ind_ω の余極限・安定 Bousfield 局所化・Thomason–Neeman・Karoubi 列
KST/LocalizingInvariants/    IsLocalizingInvariant（Sp 値）と K・BF・dg の適用だけを残す
```

名前空間は移動では変えない（move_module.py の仕様）。名前空間の付け替えは R54 として別に行い、旧名には deprecated alias を残す。

## 3. 候補（R48〜）

- **R48 基礎ブロック 7 本を Stable/Verdier と Stable/Infinity へ移す。**
  対象：`StableCategories`・`ExactEnrichment`・`StableInfinity`・`VerdierSequence`・`VerdierDiagrams`・`AdjointVerdier`。`AdjointLocalization` は F1B/Localization へ。
  影響：利用元は約 300 ファイル。変わるのは import 行だけで、名前空間は変えない。前提はない。閉包を調べた結果、新しい循環は生じない。
  検証：verify.sh と、`audit_localizing_invariants`・`audit_kst_s_construction` の公理監査。工数 2〜4h。
- **R49 Derived の一般 4 本を Stable/Exact と Stable/Verdier へ移す。**
  対象：`ExactFunctorCategory`・`ExactFunctorCategoryEquivalence`・`ExactFunctorDescent`・`StableVerdierSequence`。`RestrictedDeformationLocalization` は F1B/Localization へ。
  影響：Derived 約 10 本と NonConnective 2 本。前提はない。新しい循環も生じない（`Stable/CofiberLocalizingEdges` がすでに `F1B.Localization` を import している）。
  検証：verify.sh と `audit_derived_infinity`・`audit_infinity_stable`。工数 1〜3h。
- **R50 定義の正本を一つに決め、比較補題の置き場を作る。**
  正本は束ねない形の `IsVerdierSequence`（9 人論文の定義：充満忠実、核と像が一致、cofiber 辺での DK 局所化）とし、Stable/Verdier/Basic に置く。
  束ねた形はその abbrev にして、既存の射影名（`.inverts`・`.quotient`・`.kernel`・`.kills_inclusion`）を保つ。
  `IsStableVerdierSequence` は「完全関手として普遍的な商」として名前と意味を残し、Comparison に置く。
  比較補題「`IsVerdierSequence` ⇒ `IsStableVerdierSequence`」は新しい証明なので §5 の M1 で扱う。R50 で行うのは定義の配置だけ。
  影響：束ねた形の利用元 134 ファイルは、abbrev が型を保てば変更しなくてよい。型が変わる場合は射影を書き換える必要があるため、事前に試作して確かめる。工数 0.5〜1 人日。
- **R51 一般の安定 span pushout を SConstruction から下へ移す。**
  対象：`KST.SConstruction.StableSpanPushout` とその閉包の一般部分を Stable へ移す（R44 の SConstruction 一般 DG 基盤の抽出と同じ手順）。
  これで Verdier* の汚染経路 (a) が切れる。工数 2〜4h（閉包の大きさは未計測。実施前に測る）。
- **R52 Verdier* の分数機構から K・Fibration への依存を切り離し、Stable/Verdier/Fractions へ移す。**
  汚染経路 (b) については、`RelativeFirstRowSimplexQuotient` を Φ を使わない一般部分と Sp への適用に分ける。
  `Fibration/WeakEquivalences`・`GroupoidCompletion*` のうち Verdier* が使う一般部分を抽出する。
  汚染経路 (c) は R27（HL → KST.Spectra）の後で再計測する。
  Derived の `ActualRoof*`・`Roof*`・`WeakRoof*` と Stable の `CofiberHoDenominators` は、重複していないかを点検してから同じディレクトリに集める（統合するかどうかは点検の結果で決める）。
  前提：R48・R51・R27。影響：Fibration と LocalizingInvariants の相互参照（R2-C）と重なるため、K-B3 の調査結果と照らし合わせる。工数 32〜64h。
- **R53 厚い部分圏の一般述語を作る。**
  Stable/Verdier/Thick に、∞ 層の `IsThick`（安定かつ retract で閉じる充満部分圏）と `thickClosure`（`StableVertexClosure` と `retractClosure` の合成）を置く。
  dg 版の `dgThickClosureProperty` はこれの特殊化として書き直す。数学的な内容は保つ。工数 0.5〜1 人日。
- **R54 名前空間を付け替える。**
  移動したファイルの名前空間 `SerrePositivity.KST.LocalizingInvariants` を `SerrePositivity.InfinityCategories.Stable` に変え、旧名には deprecated alias を残す。
  R48〜R53 がすべて緑になってから行う。工数 2〜4h。
- **R55 Stable.F2Applications 層を作り、新しい数学の置き場を決める。**
  R40 の層規約に従い、Stable と Presentable の両方を使う結果（§5 の M3〜M6）はここに置く。
  前提：R37・R38（F2 と Stable の逆向き import の解消）と R31（PiCriterion の配置）。
  現状では Bousfield 局所化の閉包に KST.Spectra のモジュールが 68 本入っており、これを外さないと ∞ 層の商が KST に依存してしまう。
  中身はまだないので、ここで行うのは方針の文書化と空のディレクトリの用意だけ。工数 1〜2h。

- **R56 局所化の存在（L4、約 40 本）を F1B/Localization へ移す。**
  対象：`LocalizationResolution`・`GeneralLocalization`・`LocalizationFactorization`・`LocalizationUniqueness`・`InverseAttachment*`・`WalkingEquivalence*`・`GroupoidCompletion*`・`SimplexAttachment*`。
  閉包に KST 固有のモジュールはほとんどない。Fibration・Verdier 分数の多くがこれを import している。
  前提はない。R48 と並べて最初に行う。工数 2〜4h。
- **R57 Verdier 分数の複製（Fibration の Weak* と LocalizingInvariants の Tamme* の 4 対）を、「安定 ∞ 圏の中の pullback で安定な辺の集合」に対する一つの版にまとめる。** R52 の中で行う。

## 4. 実施順

1. R56・R48・R49（独立していて危険が小さい。所有の変更を決めてから、R 第 2 窓の最初に行う）
2. R50・R53（定義を整える）
3. R51 → R27 の後で R52（大口。R2-C と同時に行う）
4. R55（R37・R38・R31 の後）
5. R54（最後にまとめて行う）

各段の終わりに verify.sh を全緑にし、`git commit --only` で該当パスだけをコミットする。

## 5. リファクタの後に必要な新しい数学（本計画の範囲外。置き場所だけ決める）

| 番号 | 内容 | 置き場所 | 原典 |
| --- | --- | --- | --- |
| M1 | `IsVerdierSequence` ⇒ `IsStableVerdierSequence`。DK 局所化の普遍性を完全関手に制限する。完全性の判定に `isExactFunctor_of_precomp_arrowLifts` を使い、そこで必要な「矢の持ち上げ」を R52 の分数表示から得る | Stable/Verdier/Comparison | 9 人論文 II.A |
| M2 | 安定圏の cofiber 辺での局所化は安定で、局所化関手は完全である（一般形。現在は dg 版 `dgQuotientNerve_isStable` しかない）。逆向きの比較（核が厚い場合）もここで扱う | Stable/Verdier | NS I.3.3、BGT §5 |
| M3 | 有限余極限をもつ C に対して Ind_ω(C) が小さい余極限をもち、presentable である | F2/Ind（Stable は使わない） | HTT 5.3.5.14 |
| M4 | 安定 presentable 圏を、シフトで閉じた辺の集合で Bousfield 局所化すると安定になり、反射は完全になる | Stable/F2Applications | HA 1.4.4 |
| M5 | Thomason–Neeman：局所化の compact 対象は、L(compact) の retract で閉じた部分と一致する | Stable/F2Applications | Neeman 1992、9 人論文 II.A.3 |
| M6 | Karoubi 列の定義と、道 (B) による Karoubi 商 \((\mathrm{Ind}\,B / \mathrm{Ind}\,A)^\omega\) の存在 | Stable/F2Applications | 9 人論文 II.A.3、BGT §5 |
| M7 | （道 (A)）Verdier 商の存在。DK 局所化の存在は既存（R56 で移す）。これを M2 と組み合わせ、核の条件（像が厚いこと）を確かめれば得られる | Stable/Verdier | HA 1.3.4、NS I.3.3 |

道 (B) は M3〜M6 で完全な Karoubi 商を与える。Verdier 商そのもの（冪等完備化を伴わない商）を得るには、
M6 の商の中で B の像の生成する部分圏を取るか、M7 を経由する必要がある。どちらを主路にするかは、R48〜R53 の後に改めて決める。
