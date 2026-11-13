# §7 semiperfectoid 環と混標数の perfection：リファクタの提案と、形式化の計画の提案（2026-11-12）

作成：ノートのチャット（形式化の調整役ではない）。§2〜§6・§8・§10 と同じ形。**扱いは調整役が判断する。** 事実に推奨を添える。

- 基準：main 22150d511。B3 の配置案は refactor/kerodon-layout 枝（24151a43d）の `formalization-plans/stage-ii/report-bulk-w1.md`。読み取りだけのエージェントがノートの加筆 3 本、コードの見直し 1 本（件数を含む）。件数のスクリプトはノートのチャットの作業用の場所にある。規模の見立ては、明記したもの以外は推測。
- 原典（pp.55–62）の項目は Not 7.1、Prop 7.2、Cor 7.3、Thm 7.4、Rem 7.5、Construction 7.6、Lemma 7.7、Lemma 7.8、Ex 7.9、Prop 7.10、Prop 7.11、Ex 7.12、Ex 7.13、Thm 7.14、Rem 7.15 の 15 個。
- 二種類の提案：**A. リファクタ（R7-1〜R7-8）**、**B. 形式化の計画（§3 の表と §3.1 の計画上の点）**。

## 0. 規模と中身の分かれ方（確認済み）

- 対象は 136 本・74,999 行。内訳は Semiperfectoid 76 本・14,179 行、Andre 57 本・60,178 行、Prismatic/FiniteEnvelope* 3 本・642 行。**本体に sorry はない**（文字列の一致は 1 か所あるが、Audit/VarpiComparisonUnconditional:19 の docstring の中）。
- 群に分けると次のとおり。
  - (a) Thm 7.14（André）の経路：Andre の Envelope 15・OrdinaryRoots 3・Perfection 2・Transfinite 3・TorDescent・AndreFlatness。
  - (b) Cor 7.3・Thm 7.4：Semiperfectoid 10 本・3,962 行。
  - (c) W15 K5・W17 H5 の Lemma 7.7〜Prop 7.10 の古典部分：Semiperfectoid 63 本と FiniteEnvelope 3 本、計 7,508 行。内訳は Lci 19、RootRelation 17、RootFamily 5、CompletedTensor 4、Ainf 2、Discrete 2 など。
  - (d) Rem 7.15 の旧経路：Andre/PowerRootEnvelope 27 本・26,771 行（Audit 4 本を含む）。
  - (e) André の任意族版：Andre/Variants 4 本・5,186 行。
  - (f) Thm 7.4 の別証明：Semiperfectoid/RootEnvelope 3 本・3,351 行。
- 主定理の閉包に入るのは 136 本のうち 33 本・30,394 行。Andre が 25 本（すべて Thm 7.14 の閉包）、Semiperfectoid が 8 本（Cor 7.3・Thm 7.4）。**(c)〜(f) は 0 本。**

## 1. A. リファクタの提案（今あるコードを直す）

### R7-1 drafts の A3 の古典部分は本体に置き換わっている【推奨：5∞-0。R4-1・R5-1 を A3 と A2 の一部に広げる】

drafts/A3 は 2 本（DiscreteCase・LciAndQuasiregular）、96 宣言、sorry 53 か所。冒頭の基準コミットは 972bb7f53 のまま。A3 の drafts が本体の名前を引くのは `exists_perfectoidization_of_perfectPrism_quotient` の 1 件だけ。

本体側の対応は、名前・docstring・W17 報告 §11 の表で確認した。型の一致は確かめていない。

| drafts の宣言（sorry の数） | 本体 |
| --- | --- |
| `initial_of_retraction_idempotent`:55（1） | 同名の `CategoryTheory/InitialOfRetraction:53` |
| `prismOver_isIdempotentComplete`:66（1） | `PrismOver.isIdempotentComplete`（PrismRetract:127） |
| `deltaStructure_of_envelopeIso`:155（3） | `existsUnique_over_of_equiv`（DiscreteDelta:50） |
| `deltaStructure_of_discrete_pTorsionFree`:141 | 古典の芯は `existsUnique_over_of_frobeniusLift`（DiscreteDelta:35） |
| `discretePrism`:180（3）・`discretePrismBase`:189（1） | `OrientedPrism.ofDiscreteDelta`:36・`toDiscreteDelta`:65 |
| `discrete_weaklyInitial`・`exists_initial_of_discrete` | 古典の芯は `PrismOver.homOfFrobenius`:101・`exists_initial_of_primeRegular_evaluation`（PrismRetract:160） |
| `universalLciPrism`（4）・`_bounded`（1）・`lciClassifyingMap`（1） | `universalOrientedPrism`（Ex 3.4）と `exists_bounded_lciRelationEnvelope_of_classifier`（LciEnvelopeExistence:62）。普遍 lci の基底そのものとの一致は推測 |
| `lciTensorDelta`（1）・`_map_iff`（1） | `tensorDeltaStructure`・`tensorDeltaStructure_isDeltaHom_iff`（Delta/Basic/Tensor:101・135） |
| `exists_lciEnvelope`:250（1）・`IsLciEnvelope` | `exists_bounded_lciRelationEnvelope`（LciEnvelopeExistence:142）・`IsFiniteLciRelationEnvelope`:40 |
| `padicBaseAlgebra`:264（1） | `arcPadicIntMap`（ArcPerfectoidBase:406）。R5-3 (a)・BR50 で移す先と同じ |
| `ainfCoefficients`・`ainfTheta`・`ainfDelta`・`ainfData`（3） | `ainfClassical*`・`exists_ainfClassicalPrism`（AinfClassical:45〜105、AinfClassicalMaps:28） |
| `rootPolynomials`・`rootBase`・`rootX`・`rootBase_perfectoid`（1） | `rootFamilyRaw`・`rootFamilyBase`・`rootFamilyVariable`・`rootFamilyBase_isIntegralPerfectoid`（RootFamilyBase、RootFamilyPerfectoid:43） |
| `rootRelations`・`rootQuotient`・`regularSemiperfectoid` | `rootLiftRelationIdeal`・`…Quotient`・`…Completion`（RootRelationLift:50〜58） |
| `perfectedPrism`・`toPerfectedPrism`（1）・`IsCor73Comparison` | `classicalPrismPerfection`（Prism/Perfection/ClassicalPrismPerfection:34）・`IsClassicalCor73Comparison`（Cor73PrismComparison:63） |
| `rootQuotient_prismatic_perfection_eq`（2） | `ainfClassicalTheta_surjective`・`exists_rootRelationPrismaticPerfection`（RootRelationPerfection:29・52） |
| 古典部分だけ本体にあるもの：`regularSemiperfectoid_prismatic`・`rootQuotient_initial`・`lci_envelope_surjective_invert_p_universal` | `exists_rootRelationAinfEnvelope`、`exists_rootLiftRelationCompletion_initial`、`exists_rootRelationCompletedInitial`、`lciRelationConormalLinearMap_surjective`、`surjective_of_dense_dividedPower_generators_retraction` |

- 本体を指すだけで消える sorry は **約 26 か所**（53 のうち。数え方の根拠は上の表）。ほかに 6 宣言は古典部分だけが本体にある。
- **A3 は D71〜D73 の E∞ 界面への移行が済んでいない**（確認済み）。A3 の 2 本は `EInfinityTheory` も `(E := E)` も一度も使わず、`open …BarrattEccles` のまま。一方 A2 は `variable (E : EInfinityTheory)` を明示引数に取る（DerivedPrismaticCohomology:45）。そのため A3 の `derivedPrismaticCohomology_h0_ring P hP …`（DiscreteCase:79）は引数が合わない。
- **A2 の `Poly`**（AnimatedAlgebra:61）は、本体の `Prismatic.Poly`（PolynomialCategory:33、D69）と同じ名前空間・同じ定義。drafts の 8 本（A1 の 4 本、A7、Shared 2）が使っている。drafts を本体へ移すと名前が衝突する。
- A1 の `prismaticCohomology_lci_universal`（DeRhamComparisonPoly:505）は Ex 7.9 の特殊化で、どこからも使われない。A3 の側へ移す（§5 の見直しの §4 の 4 と同じ）。

### R7-2 二重の構成【推奨：(a)(b) は保守（優先）。(c) は §3 の補完と合わせる。(d) は残す】

- **(a) 忠実平坦版と並ぶ三段の系列**（確認済み）：
  - `exists_bounded_lciRelationEnvelope` と `_faithful`（LciEnvelopeExistence:142 と LciEnvelopeFaithful:209）
  - `exists_perfectoidRelationEnvelope` と `_faithful`（PerfectoidRelationEnvelope:31 と …Faithful:34）
  - `exists_rootRelationEnvelope` と `_faithful`（RootRelationEnvelope:34 と …Faithful:34）

  どの組も、忠実平坦版の結論は元の版の結論に「単位の p 完全忠実平坦性」を一項足しただけ。ところが LciEnvelopeFaithful は構成をやり直している（`exists_lciRelation_regular_completedTensor` と `exists_envelope_of_classified_ideal_of_regular` を直接呼ぶ）。非忠実平坦の系列の終点 RootRelationEnvelope は葉で、利用者は監査だけ。PerfectoidRelationEnvelope の利用者は RootRelationEnvelope だけ。RootRelationEnvelope と …Faithful は module docstring の概要が一字一句同じ。

  提案：非忠実平坦版は忠実平坦版の一行の系にする。地図の Ex 7.9 の項目 `exists_bounded_lciRelationEnvelope` の名前は残す。
- **(b) 名前のない述語**：p 冪ねじれの有界性 `∃ N, ∀ n x, p^n x = 0 → p^N x = 0` を、30 本・67 行が展開して書いている。drafts/A3 には `BoundedPTorsion`:60 がある。semiperfectoid は本体に定義がなく、drafts に二度ある（A5/SemiperfectoidCase:129 の `IsSemiperfectoid`、A3 の `IsQuasiregularSemiperfectoid.semiperfectoid` の中）。提案：二つを本体に名前つきで置く（`CommutativeAlgebra/PowerTorsion` の隣と Semiperfectoid）。
- **(c) §3 の補完との関係**：§3 の補完にある「Lemma 3.5 後半の向き付きの構成子 `OrientedPrism.ofDeltaHom`」は、実質 `OrientedPrism.ofDiscreteDelta`（DiscretePrism:36）としてもうある（δ 射の像が正則で完備なら prism）。PrismRetract・RawVariableEnvelope・LciEnvelope が使う。主張の向きまで同じかは推測。
- **(d) A_inf の模型**：本体に二つある。`ainfClassicalPrism`（Fontaine の核）と、`exists_boundedPerfectPrismPresentation` が使う `perfectDeltaPDPrism`。drafts の `ainfCoefficients` を数えると三つ。R3-5 の状態は変化なし。原典の対象なので残す。

### R7-3 層の向き【推奨：B3（BR26′・R3-2 に追加）】

- **(a) KST → BS**（台帳にない）：`KST/DerivedBlowup/UniversalRegularSequence:4` が `Andre.OrdinaryRoots.MonicRelation` を import している。中身は「独立なモニック関係は弱正則列」という 122 行の可換環論。BR26′ にあるのは CommutativeAlgebra/KoszulRegular/Powers の側だけ。提案：MonicRelation を `CommutativeAlgebra/KoszulRegular` へ移す（OrdinaryRoots/Family の多項式の補題も一緒に）。これで BR26′ の 1 件も同時に解ける。
- **(b) §7.2 の古典部分が §7.3 の André の内部に依存**（確認済み、8 辺）。使うのはどれも汎用の宣言。

  | importer | import 先 | 使う宣言 |
  | --- | --- | --- |
  | LciEnvelopeCompletedResidue | Transfinite/Colimit | `isCompletelyFlat_comp`、`principalCompletionH0_isCompletelyFaithfullyFlat` |
  | LciEnvelopeCompletedResidueFaithful | Transfinite/Colimit | `isCompletelyFaithfullyFlat_comp`、`principalCompletionH0_isCompletelyFaithfullyFlat` |
  | RootFamilyBase | Transfinite/Colimit | `boundedPrincipalCompletionAdicAlgEquiv` |
  | RootFamilyBase | PowerRootEnvelope/PowerRootPolynomial | `PowerRootPolynomial`、`powerRootExponentMonoid`、`powerRootVariableExponent` |
  | LciEnvelopePresentation | Envelope/DivisionResidue | `deltaAdjoinDivisionResidue*` の 5 宣言 |
  | LciEnvelopeRegular | Envelope/RootSource | `IteratedPDCompletionObject`、`iteratedPDH0LinearEquiv` |
  | LciEnvelopeKoszul・RootRelationPolynomial | OrdinaryRoots/MonicRelation | `monicRelation_fin_isKoszulResolution` |

  移し先：完全平坦性の部分は `CommutativeAlgebra/CompletelyFlat`（R3-2 と同じ）。完備化の部分は `HomologicalAlgebra/DerivedCompletion`。δ 除算の剰余は `Delta/Division`。
- **(c) `PowerRootPolynomial` の置き場所**（1,762 行、A[Y^{1/p^∞}] の一般論）：Rem 7.15 の旧経路のディレクトリ（閉包の外）にあるが、Prop 7.10（RootFamilyBase）、§8（`Perfectoidization/Derived/RootAdjunction`）、drafts/A3（`rootPolynomials`）の基本の対象になっている。docstring の「使われ方」はこの 3 者を挙げていない。提案：`CommutativeAlgebra/`（または Semiperfectoid/RootFamilies）へ。
- **(d)** `exists_boundedPerfectPrismPresentation`（PerfectoidPrismPresentation:47）は Thm 3.10 の主張なので `Prism/Perfectoid` へ。`DiscreteDelta` の 2 宣言は δ 環だけの補題なので `Delta/Basic` も候補（推測）。
- §7 から外への辺の現状：Prism/Bounded/PDCompletionPrism → LciEnvelopeRegular・Transfinite/Colimit と Prismatic/FlatCover → Transfinite/Tower は R3-2 で既出。§8・§10・CLMST から §7 への辺（Transfinite/Limit ← 3 本、TorDescent ← 2 本、Surjectivity ← 5 本など）は向きとして自然なので、そのままでよい。

### R7-4 置き場所【推奨：B3。配置案を細かくする】

- B3 の案は「`Lci/`（19）・`FiniteEnvelopes/`・`RootFamilies/`・`Cotangent/` 等」。しかし**本体に余接複体のコードはなく、`Cotangent/` に入るものがない**。また RootRelation 17、Ainf 2、CompletedTensor 4、Lemma 7.7・7.8 の 3 本、Cor 7.3、Thm 7.4、RootEnvelope の行き先が書かれていない。
- 項目ごとに分ける案：
  - `Discrete/`（7.7・7.8）：DiscreteDelta、DiscretePrism、PrismRetract
  - `Lci/`（7.9）：Lci 19、RawVariableEnvelope 2、CompletedTensor 4、PrismRelationQuotient、PerfectEnvelopeInitial
  - `Quasiregular/`（7.10）：RootFamily 5、RootRelation 17、Ainf 2、FontainePrism、PerfectoidWittEquiv、PerfectoidRelationEnvelope 2、FiniteEnvelope 3、PrismInitial 2
  - `Perfection/`（7.3）：Perfectoidization、PerfectPrismDivision 2、InitialPrismPerfection、Cor73PrismComparison、QuotientPerfectoidization、Product、CharacteristicP
  - `Surjectivity/`（7.4）：Surjectivity、CompatibleRoot 2、AbsolutelyIntegrallyClosedQuotient、その下に RootEnvelope/（別証明）
- FiniteEnvelopeDiagram の先頭（`IsPrismaticEnvelope.transition*`、:45〜80）は包絡の一般の関手性なので `Prismatic/Envelopes` に残し、残りを §7 へ（推測）。
- Andre は「57 本の下位分類を保持」でよい。ただし R7-3 の汎用部品は外へ出す。Andre/Perfection/DeltaAlgebra は自分の docstring に「§3 の一般論として切り出すのは今後の候補」と書いている。

### R7-5 名前空間【推奨：B3 の改名表（BR48 と同じ回）】

- Semiperfectoid 76 本の名前空間はばらばら：`…Semiperfectoid` 39 本、`…BhattScholze` 直下 21 本（＋Surjectivity）、`…Prismatic` 10 本、その他 5 本（`Prismatic.PrismOver`、`OrientedPrism`、`DeltaStructure`、`SerrePositivity` 直下 2 本）。
- **Ex 7.9 の 19 本は `BhattScholze` 直下 10 本と `Prismatic` 9 本に割れている。** CompletedTensor の 4 本も 3 本と 1 本に割れる。
- Andre/Envelope は 16 本のうち 14 本が `BhattScholze` 直下。AndreFlatness は証明済みなのに `Inputs` 名前空間（地図の 7.14 の行の注記どおり）。

### R7-6 主定理の閉包・葉・未使用の宣言・root から届かないもの【推奨：原典の項目にあたる宣言は消さない。(c) は B3 で判断】

- (a) 閉包に入るのは 33 本（§0）。**Lemma 7.7〜Prop 7.10 の古典部分は 0 本**。E3 の経路で drafts/A3 から使われる予定だが、まだ使われていない。
- (b) 葉（集約以外の importer がない）は 14 本。
  - W15・W17 の終点 6 本（利用者は stage2 監査だけ）：LciEnvelopeConormal、LciEnvelopeInvertPGenerators、PrismRetract、RootRelationAinfEnvelope、RootRelationEnvelope、RootRelationPerfection
  - 古いもの：Envelope/PDivisionSource、PowerRootEnvelope/Audit 4 本、Variants/MonicRootedExtension（root の集約からだけ）、PerfectPrismDivisionComparison、RootEnvelope/PerfectPrism
  - Lemma 7.7 の本体の宣言のうち、`existsUnique_over_of_frobeniusLift`・`existsUnique_over_of_equiv`・二つの `homOfFrobenius`・`ofDiscreteDelta_bounded` は利用者 0。
- (c) **root（既定のビルド）から届かないもの 9 本**（台帳にない）：RootEnvelope 3 本（3,351 行、10-25 に残すと決めた Thm 7.4 の別証明）、PerfectPrismDivisionComparison（579 行）、Envelope/PDivisionSource（1,025 行）、Audit 4 本。読むのは scripts の監査だけなので、既定のビルドでは一度もコンパイルされない。
- (d) 公開の宣言は 3,201 件。
  - 自分のファイルの外で本体・drafts・scripts のどこにも出ないもの 1,200 件（自分のファイルでも未使用 216 件）。
  - 外では監査だけが使うもの 1,037 件（Andre/Envelope に 669 件が集中）。
  - 群ごと（宣言／外で未使用／自分のファイルでも未使用）：PowerRootEnvelope 1,061／675／131、Variants 177／143／20、Envelope 978／93／16、Lemma 7.7〜Prop 7.10 の古典部分 262／120。
  - 全部未使用のファイル：PDivisionSource 48/48、PerfectPrismDivisionComparison 38/38、RootEnvelope/PerfectPrism 43/43、LciEnvelopeConormal 10/10、LciEnvelopeVariables 5/5、DiscreteDelta 2/2 など。

### R7-7 docstring の工程ラベル・古い記述・引用【推奨：B3 の docstring の回（BR25・BR34）。`@[cite]` の付け方に一言】

- **件数**（コメントの中だけを数えた）：
  - 「（旧 パス）」の節見出し：571 か所・59 本
  - module docstring の決まり文句「統合前の…（BS-W8 で統合）」：42 本
  - 「André E1・E2」「R1」：227 行・34 本
  - 「A1-a〜f」：81 行・19 本
  - 「B4-x」：34 行・14 本
  - K5・D36・D76・G-A3-7・G9・G10 などの工程・設計番号：44 行・20 本（W15・W17 のファイル）
  - 「drafts の … と同じ／照合」：21 行・12 本（AinfClassical:9・44・103、RootRelationLift:13〜107、RootFamilyBase:15 など）。R7-1 で drafts を本体に寄せた後は意味を失うので、数学の言葉に直す。
  - ノートを引くもの 2 本（JetKoszul:17、PDivision:30）は既存の 22 か所の一覧に入っている。
- **存在しないパスを指す記述 9 件・4 本**：AndreFlatness:19（`Andre/Transfinite/Theorem714`）、AndreFlatness:35（`AndreCompatibleRootsConditional`・`AndreSurjectivity`。BR34 で既出、未実施）、Adjoin:27（`Andre/MonicRelationRegularSequence`）、Surjectivity:488〜496 の 4 件、RootEnvelope/PerfectPrism:976。PowerRootPolynomial の「使われ方」は利用者が欠けている（R7-3 (c)）。
- **引用の注意（B3 で `@[cite]` を付けるとき）**：
  - 「Remark 7.15」は 46 本で 1,741 回（うち PowerRootEnvelope が 1,298 回）出てくるが、Rem 7.15 の主張は証明していない（地図 7.15 の行）。付けるなら `partial := component` か、「Thm 7.14 の証明」として付ける。
  - 「Proposition 7.11」は 13 本で 71 回。ほとんどが「原典の Prop 7.11 を使う証明とは異なる」という決まり文句。ただし二つの見出し（MonicCandidate:20「Prop 7.11 を R̃ に当てる部分」、DeltaAlgebra:32「Prop 7.11(2) の…部分」）は Prop 7.11 の一部を主張しているように読める。Prop 7.11 は D38 で形式化しないので、Prop 7.11 の属性は付けない。決まり文句は AndreFlatness の module docstring に一度書けば足りる。

### R7-8 設計書・地図の古い記述【推奨：調整役が直す】

- **a3-design**（11-02 のまま、W15 K5・W17 H5 を反映していない）：
  - §1 の表と §6 の単位：本体に入った部分（R7-1 の表）が書かれていない。
  - :22〜23 の前提「A1-4 の A_0」、:68〜71「停止点 3 で A1 の A₀ に特殊化」：本体は既に `universalOrientedPrism` を使う（LciEnvelopeExistence:150）。
  - G-A3-5（:152、「なし」）・G-A3-6（:153、「要確認」）・G-A3-7（:154、「なし」）：古典部分は本体にある。
  - G-A3-8（:156）：使ったのは `existsUnique_perfectDeltaPDPrismHom` ではなく `ClassicalPrismPerfection`。
  - G-A3-10 (a)（:158）：本体に `tensorDeltaStructure` がある。
  - §2.3 の「RootEnvelope の再利用」（:140〜142）と §8 の 6 の `PerfectPrismRootSource*`：W17 は RootEnvelope を使わず新しく作った。`PerfectPrismRootSource*` という名前は存在しない。
  - Prop 7.10 の S′ の単位の完全忠実平坦性が後回しになったこと（design-status:47）が書かれていない。
  - G-A3-9 は D79（P⁰ が Sp 値）に合わせていない（推測）。
- **a2-design**：
  - :8・:114「F2/Presentable の Sigma*」：今は `Kerodon/LargeInfinityCategories/…`。`InfinityCategories/F2/Presentable` は存在しない。
  - :39・:116「HA/DerivedCompletion」：今は `HomologicalAlgebra/DerivedCompletion`。
  - §2.1 の `Poly k`：本体の `Prismatic.Poly` に寄せる（R7-1）。
  - §2.2 の CAlg_A：D71〜D73 の `EInfinityTheory` 経由になったことを反映していない。
- **design-status**：A3-1〜A3-4 の行（:140〜143）が drafts と BS-D4 のことしか書いていない。R4-3 で直した :43 の注記と同じ扱いで、K5・H5 の本体（`Semiperfectoid/` の上記の宣言）を書き足す。
- **地図 items.csv**：§7 の行の宣言の場所 29 件はすべて正しい（確認済み）。気になるのは 7.1 の goal=required。qrsp（`IsQuasiregularSemiperfectoid` と `qrsp_*`）は A4〜A9 の drafts から一度も使われず（確認済み）、E3 は S′ と T しか使わない（a3-design §2.3）。special が妥当か見直す。

## 2. 台帳の項目の今の状態（§7 に関わるもの）

- **BR7（根とモニックの並行）**：未実施。W8 で統合したため、台帳が名指しするファイル（`DeltaRootFamilyRawCompletelyFlat`・`Variants/MonicRawCompletelyFlat`）はもうない。今の並行は Andre/Envelope の Root* 5 本（RootRelation・RootResidueKoszul・RootSource・RootFamilyRaw・RootFamilySource、計 5,350 行・267 宣言）と Monic*・OrdinaryRoots。**新しい事実**：Root* の 5 本は Thm 7.14 の閉包に入っているのに、Root* 以外の André のファイルが使う宣言は 20 だけ（RootRelation 8、RootSource 8、RootFamilySource 3、RootResidueKoszul 1、RootFamilyRaw 0）。X^p − b の側の B4 旧経路（RootEnvelope 3 本）は root から届かない。
- **BR10・BR35（Variants）**：変化なし。重複の対は Auxiliary:1541 と Tower:1172、RootedExtension:1584 と Tower:1463 で、行番号も同じ。Variants は 4 本・5,186 行・177 宣言で、外で未使用 143。届くのは root の集約（BhattScholze.lean:477）からだけ。Variants/Auxiliary が PowerRootEnvelope の 6 本を import していて、多くの PowerRootEnvelope のファイルにとって root へ届く経路になっている。
- **BR11（Rem 7.15 の旧経路）**：決定どおり残っている。27 本・26,771 行で閉包には 0 本、Thm 7.14 からも 0 本。**新しい事実**：本体の外の 5 本（Delta/DividedPower/FrobeniusDivisionRegularSequence、Prism/Basic/UniversalOriented、Prism/Basic/Construction61Frobenius、Prismatic/CompletedFreeDeltaFlat、Perfectoidization/Derived/RootAdjunction）と Prop 7.10 の RootFamilyBase が、このうち 9 本（10,764 行）を引き込む。宣言 1,061 件のうち外で未使用は 675 件。
- **BR12**：変化なし。旧い適用形 `exists_surjective_perfectoidization_of_complete_torsionFree_quotient`（Surjectivity:553）・`surjective_of_isPerfectoidization_of_complete_torsionFree_quotient`（:575）は監査（audit_bhatt_scholze_b4・audit_clmst_b3・audit_axioms）だけが使う。rooted 系列（`…_of_rootedKernel` など）も監査だけ。
- **BR13**：(a) は変化なしで 6 か所：RootSource:274、RootFamilySource:247、MonicCandidate:976、ArbitraryFamily:203、RootEnvelope/Source:267、PowerRootEnvelope/Unconditional/Residue:623。(b) **`exists_perfectoidTrialPrism` を直接使って手で場合分けしているのは、台帳の 5 か所ではなく 6 か所**（行番号は少しずれた）：Tower:1186、Variants/Auxiliary:1504、Variants/RootedExtension:1600、RootEnvelope/PerfectPrism:1004、Perfectoidization:398、**Perfectoidization:283（T の側、台帳にない）**。`exists_boundedPerfectPrismPresentation` を使うのは 4 本（PerfectoidRelationEnvelope:48・…Faithful:53・InitialPrismPerfection:72・AinfClassical:143）。
- **BR14**：変化なし。Audit の 4 本は `scripts/audit/bhatt_scholze.lean` だけが import する。
- **BR36**：変化なし。三つは Tower:1083（step を仮定する版）、Tower:1509、AndreFlatness:58（Inputs）。
- **BR26′**：記載の 2 件は変化なし。R7-3 (a) の KST の importer を足す。
- **BR34**：AndreFlatness:19・35 は未実施。**BR42**：変化なし（定義 `QuotientPerfectoidization` は Perfectoidization:441 にある）。**R3-2・BR41**：変化なし。**R3-5（A_inf の模型二つ）**：変化なし。**BR50（R5-3 (a)）**：`arcPadicIntMap` の移動は drafts/A3 の `padicBaseAlgebra` の sorry も解く（新しい事実）。
- **design-status:47 の後回し (1)（S′ の単位の完全忠実平坦性）**：変化なし。不足は W17 報告 §16 の 3 点で、Codex の見積もりは約 700〜1,000 行。
- 台帳にない新しい事実のまとめ：R7-1 の全部、R7-2 (a)〜(c)、R7-3 (a)〜(d)、R7-4 の `Cotangent/` の空振り、R7-5、R7-6 (c)、R7-7 の存在しないパスと引用の注意、R7-8。

## 3. B. 形式化の計画の提案（新しく形式化する項目）

| 項目 | 今あるもの・要るもの | 規模 | 依存 | 推奨 |
| --- | --- | --- | --- | --- |
| Not 7.1 semiperfectoid | 本体に名前がない（定理ごとに展開して書いている）。drafts に二つ | 小（100 行以下） | — | 入れる（5∞-0、R7-2 (b)） |
| Not 7.1 qrsp | drafts/A3:277（四条件、D39、W9-I-32）。要るもの：基底 ℤ_p の `cotangentWedge 1`（A2-3）、ℤ_p 作用（BR50） | 定義は小 | 5∞-4（A2-3）、M13 | 定義は A3 の段で入れる（原典どおり）。E3 では使わない（R7-8） |
| Prop 7.2 | 本体は代数的な二段（δ 除算と d ねじれの除去）だけ | — | — | 入れない（D37） |
| Cor 7.3 | 存在・普遍性は一般の semiperfectoid で本体にある。S′ では始 prism の完全化との一致もある。Δ^init との一致はない | — | — | 済（特別な場合）。Δ^init の部分は入れない（D37） |
| Thm 7.4 | 証明済み（André 経由。別証明は RootEnvelope） | — | — | 済 |
| Rem 7.5 | なし | — | — | 入れない |
| Construction 7.6（A2） | drafts 4 本・1,038 行・宣言 128・sorry 59 か所。G-A2-1（Kerodon の Sigma*）はある。G-A2-2（t 構造）・G-A2-3（完備化の ∞ 関手）は M13 で本体にない（drafts/DerivedGeneral 3 本・sorry 24）。G-A2-4 は ⑤a の 5a-3・5a-4 | 大（設計書に見積もりなし） | 5∞-3b、5a-3・5a-4、**M13** | 入れる（5∞-4）。`Poly` を本体の版に（5∞-0）。(2)(3) の層性は入れない |
| Lemma 7.7 | (1) の特別な場合、(2)、(3) の古典部分（D36）は本体にある。残るのは Δ_R との同一視（離散な Δ の H⁰、RΓ の極限の脚、S2）と G-A3-9（φ が mod p で Frobenius、M14 と D79） | 小〜中 | 5∞-2、5∞-4、5a-8 | Δ 版は入れる（A3 の段）。(1) の一般形（W₂）は入れない（D36） |
| Lemma 7.8 | 一般形で証明済み（CategoryTheory/InitialOfRetraction:53） | — | — | 済。drafts の重複は 5∞-0 で消す |
| Ex 7.9 | 包絡の側は原典の形（R は有界、D76）で本体にある。G-A3-7 の古典の入力もある。残るのは Δ_{R/A} ≅ 包絡（G-A3-1 Koszul 正則な商の余接複体、G-A3-2 décalage、G-A3-7 の導来の部分、G-A3-10 (b)、A2 (4)(5)、HT filtration） | 中〜大（a3-design の「最重量」） | A3 の段、5∞-4 | 入れる（T の場合と普遍の場合） |
| Prop 7.10 (i) T・S′ の Δ との同一視 | 古典の包絡・始性・完全化は本体にある。残るのは G-A2-10（完全基底の比較）、filtered 余極限（A2 (5)）、離散性 | 中 | A3 の段 | 入れる（E3 の A5-2 が `rootQuotient_prismatic_perfection_eq` を使う） |
| Prop 7.10 (ii) S′ の単位の p 完全忠実平坦性 | 本体にない。有限段の忠実平坦性と遷移はある（FiniteEnvelopeDiagram・RootRelationFiniteEnvelopeDiagram）。不足は W17 §16 の 3 点 | 約 700〜1,000 行（Codex の見積もり） | なし（古典、∞ に依らない） | 補完（後回し、§8）。待ちの空いたレーンで |
| Prop 7.10 (iii) 一般の qrsp の離散性・平坦性 | drafts の `qrsp_isDiscretePrismatic`・`qrsp_completelyFaithfullyFlat`（sorry）。G-A3-2 と、HT filtration の平坦な余核による Fil₀ の純粋な包含（W17 §11） | 中 | A3 の段 | 後回し（E3 では使わない） |
| Prop 7.10 (iv) 一般の qrsp の始性 | drafts の `qrsp_initial`（「別単位」、W9-I-43） | 中 | (iii) | 入れない（必要が出たら後回しの扱いに） |
| Prop 7.11・Ex 7.12・7.13 | なし。quasisyntomic の理論（A2 の (2)(3)）が要る | 大 | — | 入れない（D38） |
| Thm 7.14 | 第一文・第二文とも証明済み | — | — | 済 |
| Rem 7.15 の主張（mod p で ind-syntomic な被覆） | 構成の部分（pd の計算）は PowerRootEnvelope にある。syntomic の定義は Mathlib にも本体にもない | 中〜大 | — | 入れない |

### 3.1 計画の上で気づいた点

1. **A3 に段がない**（確認済み。stage-ii-second-half に「A3」は一度も出ない）。一方で drafts の依存は次のとおり。
   - A4（5∞-5）が A3 の `IsDiscretePrismatic`・`deltaStructure_of_discrete_pTorsionFree` を使う。
   - A5（5∞-6）が `prismMapOfDiscrete`・`rootQuotient_prismatic_perfection_eq` を使う。

   **推奨**：「5∞-4c A3：Lemma 7.7 の Δ 版、Ex 7.9・Prop 7.10（T・S′）の Δ との同一視、G-A3-1・2・9・10、G-A2-10」を足す。依存は 5∞-2、5∞-4（A2-3・A2-4）、5a-8（M14、G-A3-9）。5∞-5・5∞-6 の前に置く。
2. **M13（plan-draft の A-2：D(A) の t 構造と完備化の ∞ 関手）にも段がない**（確認済み）。A2-3（HT filtration）、A3 の離散性、A4 の G-A4-4 の前提なのに、5∞-4 の依存に入っていない。5∞-1 の隣（BS の担当、11-03 の分担どおり）か ③ に置く。
3. **A3 の古典の残りは ∞ を待たずにできる**（5∞-3a と同じ考え方）。5∞-0 に足すもの：
   - R7-1（drafts/A3 を本体に寄せ、約 26 か所の sorry を外す。EInfinityTheory への移行も）
   - A2 の `Poly` を本体の版に
   - R7-2 (b) の名前つきの述語（semiperfectoid、有界 p 冪ねじれ）
   - BR50 で `padicBaseAlgebra` を解く

   S′ の単位の完全忠実平坦性（約 700〜1,000 行）は補完として、空いたレーンの仕事にできる。
4. **⑤∞ との関係**：§7 の E3 の経路はすべて 5∞-4c（新設）に集まる。Thm 7.14・Thm 7.4・Cor 7.3 は済んでいて閉包に入っている。5∞-4b（Thm 6.4）は A3 の Ex 7.9 に依らない。A1 の `prismaticCohomology_lci_universal` は葉（確認済み）。

## 4. 件数（スクリプトで数えた）

- 対象 136 本・74,999 行。sorry 0。閉包 33 本・30,394 行。Thm 7.14 の閉包 25 本、Thm 7.4 の閉包 29 本。root から届かないもの 9 本。葉 14 本。
- 公開の宣言 3,201 件。外で未使用 1,200 件（自分のファイルでも未使用 216 件）、監査だけが使う 1,037 件。
- drafts：A3 は 96 宣言・sorry 53 か所（本体を指すだけで外せるものが約 26）。A2 は 128 宣言・sorry 59 か所。drafts から本体の §7 の名前を引くのは 1 件。
- 有界 p 冪ねじれの展開形：30 本・67 行。存在しないパスの記述：9 件・4 本。「Remark 7.15」の出現 1,741 回・46 本。「Proposition 7.11」の出現 71 回・13 本。
- `exists_perfectoidTrialPrism` の直接の利用 6 か所。BR7 の Root* 5 本で André が使う宣言 20。
- 地図 items.csv の §7 の行の宣言 29 件は、場所がすべて正しい。

## 5. ノートの側（参考）

1. ノート：§7 の全 15 項目を見出しと主張・Lean・証明の囲みにした（07 章、番号 7.1.n〜7.3.n）。Thm 7.4 は証明の順に合わせて §7.3 の最後（定理 7.3.6）に置いた。章末の項目の表と D 表は外し、D 番号は各項目の「原典との差」に引いた（D11 は Thm 7.4、D12 は Thm 7.14、D36 は Lemma 7.7、D37 は Prop 7.2・Cor 7.3、D38 は Prop 7.11・Thm 7.14・Rem 7.15、D39 は Not 7.1、D76 は Ex 7.9 など）。
2. 補った筋（「補った筋あり」の印）は 10 項目。担当が D の評価に書き入れた「どちらが簡単か」は、D 番号の決定がユーザーのものなので、違えば直す。
3. 地図 items.csv（56decc02b）：7.3 に `exists_perfectoidization_of_semiperfectoid_quotient`、7.7 に `PrismOver.homOfFrobenius`（`OrientedPrism.homOfFrobenius` と区別）、7.9 に `exists_bounded_lciRelationEnvelope_faithful`、7.10 に `existsUnique_perfectEnvelopeHom`・Cor73PrismComparison・InitialPrismPerfection の宣言・`rootRelationCompletedQuotientMap_surjective` を足し、S′ は f_j=0 の場合だけと注記した。7.15 の note に `exists_monicRootPerfectoidExtension` の場所（Tower:1172）を書いた。R7-8 の 7.1 の goal=required の見直しは、地図の goal の判断なので手を付けていない。
