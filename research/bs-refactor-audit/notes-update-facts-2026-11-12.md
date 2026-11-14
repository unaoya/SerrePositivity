# BS ノート本文の更新（11-12 夜）で分かったコードについての事実

作成：ノートのチャット。`exposition/ja/bs/` の 02〜10 章の本文を main（aa906d060 前後）に合わせて書き直したとき、読み取りだけのエージェント 4 本が気づいた事実。ノートには書いていない。**事実だけで、推奨や扱いは書かない**（扱いは形式化の調整役）。宣言の位置は各エージェントが grep で確かめたもの。

## 1. 古い docstring・見出し

- `BhattScholze/Delta/Extension/DeltaLocalization.lean:19`：「今は主定理の経路にない。Example 2.21（A1）で使う予定」。今は `Delta/Distinguished/Universal.lean` が使う。
- `BhattScholze/Delta/Free/FreeDeltaFrobeniusFlat.lean:29`：「今は監査だけが読む。…使う予定」。今は `Universal`、`FrobeniusPushout`、`CrystallineTensorRegularity` が import する。
- `BhattScholze/Andre/AndreFlatness.lean:19`：`Andre/Transfinite/Theorem714.lean` を指す（今は `Transfinite/Tower.lean` の節）。
- `BhattScholze/Semiperfectoid/Surjectivity.lean` の SemiperfectoidSurjectivity 節の docstring：統合で消えたファイル名（`Semiperfectoid/AndreSurjectivity`、`Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity`、`Semiperfectoid/PerfectoidizationSurjectiveMap` など）を指す。
- `BhattScholze/Almost/PerfectoidAlmost.lean` の module docstring：「BS 著者版 Proposition 10.4 の全体は A8」。要る同値は今 `Almost/AlmostTensorForward.lean`（`isAlmostZero_iff_completedTensor_isZero`）にある。
- `BhattScholze/Perfectoidization/Derived/Interface.lean`：旧名の節見出し「旧 PerfectoidizationInterface/Interface.lean」が残る。

## 2. 同じ主張・同じ名前

- `Andre.exists_monicRootPerfectoidExtension`（`Andre/Variants/Auxiliary.lean:1541`）と `Andre.Transfinite.exists_monicRootPerfectoidExtension`（`Andre/Transfinite/Tower.lean:1172`）は同じ型の主張で、二重に証明されている。
- `exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed` が三つ：`Andre.Transfinite`（Tower.lean:1083、step を仮定に取る版）、`Andre`（Tower.lean:1509、仮定なし）、`Inputs`（AndreFlatness.lean:58）。
- `freeDeltaFrobenius_isCompletelyFaithfullyFlat`（`Delta/Free/FreeDeltaFrobeniusFlat.lean:339`）は自分のファイルの外から使われない。同じ「Frobenius の p 完全平坦性」を `Prismatic.crystallineCompletelyFlat_frobenius`（`Prismatic/CrystallineTensorRegularity.lean:206`）がより一般の形で証明し直している。
- Lemma 2.38 の r=1 の旧版が一般版と並ぶ：`Delta/DividedPower/PrincipalDP*`（1,547 行）、`Andre/Envelope/PDivision` の `deltaPDivisionRaw_p_mul_injective`・`deltaPDivisionRawPrincipalEquiv`。一般版は `RegularSequencePD*`・`FrobeniusDivision*`。
- `exists_perfectoidization_of_finite` が二つ：`Inputs/Perfectoidization.lean:23`（`Algebra.FinitePresentation` を仮定、後者を包む互換の入口）と `Perfectoidization/Derived/IntegralExistence.lean:491`。
- 同じファイルに同じ名前が二つ：`exists_perfectoidization_of_integral`（`IntegralExistence.lean:422` 界面を引数に取る版、`:467` 引用した界面を使う版）、`perfectoidization_excision_isPullback`（`Derived/Excision.lean:499`・`:555`）。名前空間か引数でだけ区別される。
- `isCoproduct` が二つ：`Prismatic/PrismaticFrameCoproduct.lean:56` と `Prismatic/CechAlexanderCoproduct.lean:49`（名前空間は別）。
- `baseExtension` が `Perfectoidization/Derived/ArcPerfectoidBase` と `DifferentialGraded/Resolution/FixedObject.lean:469` に（名前空間は別）。
- 有限完全 Tor 振幅の定義が三つ：`drafts/A1/HodgeTateComparison.lean:210` の `HasFiniteCompleteTorAmplitude`、`drafts/A0/BaseChange.lean:60` の `Derived.HasFiniteCompleteTorAmplitude`、本体の `HasCochainCompleteTorAmplitude`（`HomologicalAlgebra/CochainCompleteTorAmplitude.lean:37`）。
- drafts と本体の重複：drafts の `bockstein_sq_zero'`（`drafts/A1/HodgeTateComparison.lean:358`）は本体の `bockstein_sq_zero` と同じ型 `BetaSquareZero`。`cechIndex` が `drafts/A0/CechAlexander.lean:58` と本体 `Prismatic/CechAlexanderEnvelopeData.lean:32` に同じ定義で。
- drafts の `Construction61Hypotheses`（`drafts/A1/HodgeTateComparison.lean:163`）は通常の平坦性のままで、本体の D77 の形と二つが並ぶ（D77 の決定どおり）。

## 3. 層の向き

- `Delta/DividedPower/FrobeniusDivisionPD.lean` が `Prismatic.CrystallineTensorRegularity` と `Andre.Envelope.PDivision` を import する。
- `Delta/DividedPower/FrobeniusDivisionRegularSequence.lean` が `Andre.PowerRootEnvelope.Completion` を import する。

## 4. 名前の紛らわしさ

- 定義 `QuotientPerfectoidization` は `Semiperfectoid/Perfectoidization.lean:441` にあり、同名のファイル `Semiperfectoid/QuotientPerfectoidization.lean` の中身は別の主張（`surjective_perfectoidization_of_quotient`）。
- `perfectoidIdeal`（単項 J=(g) の核、`PerfectoidIdeal/Basic.lean:37`）と `perfectoidKernel`（一般の J の核、`Almost/AlmostConnectivity.lean:38`）。後者の根基不変性の定理の名前は `perfectoidIdeal_radical`。
- `IsAlmostZero`（加群、`CommutativeAlgebra/Almost/Basic.lean:38`）と `IsJAlmostZero`（複体、全コホモロジーが almost 零）は別。
- `Perfectoidization/Derived/ArcPerfectoidBase` の `perfectoidBaseRing`（ℤ_p[p^{1/p^∞}]^∧）を docstring で「R₀」と呼ぶが、設計とノートの R₀ は底変換した環で、コードでは `baseExtension`（S₀）。

## 5. 置き場所

- S′ の有限段の図式の 3 ファイル（FiniteEnvelopeDiagram・RawColimit・Completion）は `BhattScholze/Prismatic/` にあり、残りの T・S′ のファイルは `Semiperfectoid/` にある。
- `idealTensorEquiv`・`idealBaseChangeEquiv`（`Prism/Basic/Rigidity`）は Rigidity.lean の外から使われない。

## 6. 地図・設計との食い違い（地図は 11-12 夜に直したもの以外）

- 地図は 11-12 夜に次を直した：2.6・2.36・2.42・3.7・3.13・4.20・4.22（design_only → drafts、drafts/A0/BaseChange に型がある）・7.14（仮定なしの Tower.lean:1509 を挙げる）。
- 直していないもの：Not 7.1（ノートの表は「済」、地図は drafts）。Lemma 4.8（ノート本文は「Rem 7.15 の照合のために作られ主経路外」、地図は「A5 の完全 site ≃ Perfd に使う」）。どちらが今の状態かはエージェントが判断できなかった。
- 03 章の D8 の欠点「Mathlib の `fontaineTheta` と形が合わない」は、`exists_fontaineCompatibleWittEquiv`（`WittVector.fontaineTheta` を使う）で一部解消している。D 表の判断は変えていない。
- D 番号のない原典との差（ノートには差として書いたが、新しい D 番号は付けていない）：Ex 2.21 の係数環は ℤ の局所化（\(\mathbb Z_{(p)}\) 係数でない）。Rem 2.37 は通常の環の Tor で述べる。Lemma 3.7 (2) は通常の導来圏 `DerivedCategory (ModuleCat A)` で述べる。Cor 3.12 の層条件は環値前層の形で、高次の消滅は Čech の完全性で述べる。Lemma 2.36 (a) は原典の Frobenius の忠実平坦性でなく p 完全平坦性からの押し出しで示す。
