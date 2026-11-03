# BS-D5 基盤側 drafts の報告

## 第 1 部　停止点 1・DerivedGeneral

開始基準は main `dc77a84dd`。入口表 §1.1〜§1.3 の 14 件を具体化した。開始基準で結論が `True` だった宣言を一件と数え、分割・補助宣言は重ねて数えていない。

| ファイル | 件数 | 具体化した宣言 |
| --- | ---: | --- |
| `CompletionFunctor.lean` | 5 | `completion_isReflective`、`completion_tensor_koszul`、`completion_exact`、`complete_colimit`、`completedBaseChange` |
| `Truncation.lean` | 5 | `truncationLE_counit`、`truncation_cofiber`、`tStructure_axioms`（直交性・shift・分解に分割）、`truncationLE_of_isConnective`、`derived_nakayama` |
| `ScalarRestriction.lean` | 4 | `derivedInfinityBaseChange_restrictScalars_adjunction`、`cAlgBaseChange_restrictScalars_adjunction`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0` |

### 定義と新設した入口

* **CompletionFunctor**　`completeAt a x` は A2 と同じ主元の `IsComplete`、`IsDerivedComplete A s x` は有限集合 `s` の各元での完備性。既存の `completeSubcomplex` と `completion` に `s` を渡す。新設は `completeAt`、`completionReflection`、`completionUnit`、`cAlgCompleteSubcomplex`、`cAlgCompletionReflection`、`cAlgCompletion`、`cAlgCompletionUnit`。二つの反射は随伴を含み、単位にはその `.unitHom` を使う。`complete_colimit` の結論の圏は完備部分圏。`completion_tensor_koszul` は生成元の列と `Set.range a = ↑s` を受け、単位を代表する辺の鎖写像を `koszulFunctor` で写したホモロジー射の `IsIso` を述べる。
* **Truncation**　新設は `componentEdge`、`truncationLE_counit_h`、`truncationLE_step`、`truncationLE_step_counit`、`discreteModuleEmbedding`、`cohomologyLayer`、`tStructure_orthogonal`、`tStructure_shift`、`tStructure_decomposition`。切り捨ての隣接射と余単位の合成を指定し、その射の cofiber を Hⁿ(X)[−n] と比較する。コホモロジーには一般基盤の `derivedInfinityHomology`・`derivedInfinityHomologyMap` を使う。BS 界面の `H` と同じ導来同値・ホモロジー関手である。`derived_nakayama` の入力は `s`、その列表示、完備性、semifree 代表の `koszulComplexOn` の全ホモロジーの消滅。
* **ScalarRestriction**　二つの随伴と完備化比較は、単位や比較射を取り出せるデータを返す。新設は `cAlgH0Ring`、その `CommRing`・`Algebra S` インスタンス、`cAlgRestrictScalars_h0_base`。A4 と同じ cofibrant 代表の実際の H⁰、`homologyCommRing`、`homologyAlgebra` を使った。最後の補題は H⁰ の環同型と基底環の構造射の可換性を指定する。

### A 側の呼び出しと渡す引数

行番号は A 側の開始基準。実コードで呼び出している場合と、証明の穴・説明から今後接続する場合を区別した。

| A 側 | 基盤の入口と接続 |
| --- | --- |
| A2/DerivedPrismaticCohomology:58,63,70–74、A2/HodgeTateFiltration:52,58,60 | A2 の `completeAt` は基盤と同じ引数順。主元なら `completionReflection k {p}`、二元なら `cAlgCompletionReflection A {p,d}` の左随伴・単位を使う。二元集合での所属と A2 の連言の同値で部分圏を対応させる。 |
| A1/CrystallineInput:130、A1/DeRhamComparisonPoly:44–50、A1/HodgeTateComparison:220–225 | A1 が A2 の `completeAt` を使う箇所。`primeAlgReflection` は `cAlgCompletionReflection k {p}`、`moduleReflection` は `completionReflection A {p,d}` の特殊化。 |
| A2/BaseChangeAndTensor:25,83–86,98–104 | `completedBaseChange f s` は D(A) → D(B) の `derivedInfinityBaseChange f ≫ completion B (s.image f)`。A2 での同名参照は説明のみ。`completedPrismBaseChange` の実コードは CAlg の包含・`cAlgBaseChange f.toRingHom`・標的の反射を合成する。`perfectBaseComparison` の証明では `(cAlgBaseChange_restrictScalars_adjunction f.toRingHom).unitHom` を使う。 |
| A2/HodgeTateFiltration:91,97–101,138–151 | `truncationLE A i` は従来どおり。`hodgeTatePoly_bounded` では `truncationLE_of_isConnective A n x hx` の余単位の可逆性から頂点同型を得る。`hodgeTateTower` の穴から `truncationLE_step A i`・`truncationLE_counit A i` と合成式を使う。`truncation_cofiber A n x` が隣接段の比較。 |
| A4/Perfectoidization:155,202–211 | `reflectCompleteCAlg` は CAlg 反射の第 1 射。`restrictFrobeniusTowerColimit` は既存の `cAlgRestrictScalars_isColimitCone_of_bijective`（完全基底の Frobenius）。`restrictFrobeniusCompletion` の台は `derivedInfinityRestrictScalars_completion φ I J h`、ここで I = J = {p,d}、h は φ(I) と J の生成イデアルの根基の等号。CAlg の比較は忘却との両立と完備反射の普遍性で持ち上げる。 |
| A4/Perfectoidization:252,266–272 | 三件目の `restrictH0Equiv f x` は `cAlgRestrictScalars_h0 f x`、`restrictH0Equiv_base` は `cAlgRestrictScalars_h0_base f x`。A4 の `cAlgH0Algebra` は構造射も束ねた `A_R A`。台の環と代数構造を基盤から取れる。 |
| A5/StrongDescent:126–128 | `prismScalarExtension q` が選ぶ左随伴の証人は `cAlgBaseChange q` と `cAlgBaseChange_restrictScalars_adjunction q`。忘却後の比較は既存の `cAlgBaseChange_forget q`。 |
| A5/SemiperfectoidCase:150–158、A5/StrongDescent:111–121 | `derived_nakayama A s a ha x hx hKos` は消滅判定。前者の d 進の場合は一元の列。後者の上界判定では Koszul の filtration と完備性も使う。いずれも証明の方針からの参照。 |

`cAlgH0Algebra` の型や引数は今回変えていない。中身の段階で環の台を読み替える箇所は A4/Perfectoidization:252,260,267,271–272,277,306,322,336、A4/InterfaceFields:199,206,233、A5/SemiperfectoidCase:176,206、A7/DiscreteCore:55–56,69、A7/UniversalProperty:47、A8/IntegralDiscreteness:113,128,327。上記以外の 14 件の旧名への直接呼び出しは A0〜A9 で見つからなかった。

### 入口表の訂正・要確認・検査

* **D5-01**（`761bf6a19`）　`derivedSuspensionShiftObjectIso` により Σ = [1]。したがって ΣX の上界は n−1。τ^{≤n}X → X の cofiber は τ^{≥n+1}X で、同じ正方形が pullback にもなる。
* **D5-02**（`f7cfe33e5`）　`discreteEmbedding` の始域は通常の A 代数。加群の埋め込みを `nerveMap (moduleSemifreeResolutionFunctor A) ≫ closedNerveInclusion A (Semifree A)` で定義した。停止点 2 の完備微分形式にもこの入口を使える。shift は hD(A) 上の `loopFunctor`／`suspensionFunctor` を対象に反復している。
* 今回の未確定名・× として残した宣言は 0 件。反射・切り捨て・係数制限の証明は M13／M13-CAlg 待ち。draft 同士の import は従来どおり、取り込み先が決まるまで依存先をコメントで指定した。
* コメントを除いて開始基準と照合し、DerivedGeneral の結論 `True` は 14 → 0。drafts 全体では 53 → 39（Shared 28、Sheaves 11）。実 import のパス、括弧、新規 axiom がないこと、`git diff --check` を確認した。ビルド・Lean の型検査は行っていない。

## 第 2 部　停止点 2・Shared

停止点 1 の検収（`c992a4222`）後、Shared の名前つき宣言で結論が `True` だった **28 件中 23 件**を具体化した。指定五本と、D5-05 で許可された CupProduct の既存の入口を編集した。A0〜A9・Sheaves は読み取りのみ。

| ファイル | 開始時 | 型を付けた件数 | 結論が `True` の残り |
| --- | ---: | ---: | ---: |
| CosimplicialBockstein | 2 | 2 | 0 |
| CosimplicialEInfinity | 5 | 4 | 1 |
| DeRhamPolynomial | 1 | 1 | 0 |
| EInfinityPowerOperation | 4 | 4 | 0 |
| Descendable | 16 | 12 | 4 |
| 合計 | 28 | 23 | 5 |

指示書 §1 の「22 件」との差は Descendable の小計による。入口表 §1.7 の 16 件から、内部 Hom 待ちの 2 件と完備テンソル待ちの 2 件を除くと 12 件。構造体の欄と、すでに型がある定義の修正はこの件数に含めていない。

### 型を付けた宣言・新設した入口

* **CosimplicialBockstein・CosimplicialCupProduct**　`bockstein_leibniz` は次数 i,j の cup に対する符号 (−1)ⁱ を含む式、`bockstein_natural` は正則元を正則元に写す余単体的射についての等式とした。新設は `quotProjection`、`quotPowMap`、`cohomologyEquivModuleHomology`、`cupBockstein`。商の標準射を使い、係数環 k の作用を短完全列の三項に明示した。連結準同型を加法群の cup 側へ運ぶ際は既存の `cohomologyEquivHomology` を経由する。
* **CosimplicialEInfinity**　新設は `totEInfinityFunctor`、`totDiagram`、`totEInfinityCone`、`totEInfinity_forget_cohomology`、`totEInfinity_forget_negative`。`totEInfinity A X` は関手の頂点での値、`totEInfinity_map A f` は同じ関手で写した辺。`totEInfinity_forget` は各非負次数で A 加群の交代余面複体のホモロジーとの同型を与える。負次数では消滅する。`totEInfinity_isLimitCone` では錐の頂点を Tot に指定した。`derivedGlobalSectionsCAlg_eq_totEInfinity` は層である環の前層、弱終対象、標準射影つきの Čech データから RΓ とその余単体模型の Tot の `VertexIso` を返す。Tot 関手自身の始域は余単体的 A 代数の圏の通常の nerve。小さい Δ の nerve だけを項の図式で持ち上げる。
* **DeRhamPolynomial**　`completedForms_eq_derivedCompletion_of_boundedTorsion k T p i hk` の左辺は `ModuleCat.of k (forms k T i)` を `discreteModuleEmbedding k` で埋め込み、`completion k {(p : k)}` を適用したもの。右辺には完備形式の同じ埋め込みを置いた。`IsBoundedPrism` の定義を確認したところ、ねじれの条件は「ある N が任意の p 冪ねじれ元を pᴺ で消す」という存在文であり、そのまま `hk` に用いた。
* **EInfinityPowerOperation**　`powerOperationZero_zero`・`_natural`・`_natTrans`・`_eq_frobenius_tot` を具体化した。π₀ の環は定義上 `cAlgH0Ring X` で、`homotopyZeroRingEquiv` に沿って P⁰(x) = xᵖ と述べる。新設は二つの群・環インスタンス `homotopyZeroRing`・`homotopyAddGroup`、`homotopyZeroRingEquiv`、`homotopyCohomology`、`homotopyMap`、`restrictHomologyAddEquiv`、`powerOperationZero_component`・`_primeField`、`frobeniusRestriction`、`discreteFrobenius`、`cosimplicialFrobenius`、`totRestrictFrobeniusIso`、`powerOperationZero_eq_frobenius_discrete`。自然変換の標的で係数を制限し、その成分が各 πₙ の加法的 P⁰ を誘導する式を添えた。
* **Descendable**　(a) 押し出し、(b) 二単体で指定した合成、(c) テンソル、(e) M = R の Amitsur 降下、(g) index の一様な上界 n から逐次余極限での上界 2n、単位との一致、有限表示忠実平坦の場合を型にした。`IsThickTensorIdeal` の有限余極限・retract・正負の shift の欄も具体化した。新設は `unitAlgebra`、`hasDescentIndexLEOver_pushout`、`algebraArrow`・`algebraArrowEdge`、`isDescendableOver_tensorMaps`、`augmentationIndexCone`、`amitsurStar`、`amitsurTermCone`、`augmentedShape`、`amitsurAug`、`AmitsurData`・`AmitsurData.aug`、`DiscreteSource`。増大と各段の余積の脚は一つの増大図式から取り、[−1] の上で n+1 個の [0] を貼った標準余錐の余極限性を要求した。射の塔は射の ∞ 圏に一つの余極限錐をとるので、両端の余極限を結ぶ射も指定される。

### A 側の呼び出しと引数

行番号は `c992a4222` の A drafts。各名前について、実コードの呼び出しと証明予定の参照を区別した。

| A 側 | 渡す引数・利用の仕方 |
| --- | --- |
| A1/HodgeTateMap:72–82,153,171 | `cohomologyEquivHomology X i` の順序は同じ。A1 の `moduleCohomologyBridge` と `bockstein` の一般形が `cohomologyEquivModuleHomology` と `cupBockstein`。Leibniz 則には `C d hd_nat hd_reg k ι i j a b` を渡す。自然性は同じ先頭の六引数に標的の環・元・自然性・正則性、射と元の像の式、次数と類を加える。標的の k 作用は ι とその射の合成。 |
| A1/CrystallineInput:249–255、A1/DeRhamComparisonPoly:104,115–116、A2/DerivedPrismaticCohomology:148,154–157 | 実コードの `totEInfinity A X` は同じ引数。A1 の `pdTotMap` は `totEInfinity_map k ((pdPolynomialFunctor p k).map f)` の辺を h 圏に送る。A2 の比較には `totEInfinity_isLimitCone A X` と S3。一般形 `derivedGlobalSectionsCAlg_eq_totEInfinity A J hJ hA O hO U hU d` は `d.obj.rightOp ⋙ O` を全化する。 |
| A2/HodgeTateFiltration:187–195 | `polyForms_boundedComparison` の穴では k = A/d、T = Fin n とし、`completedForms_eq_derivedCompletion_of_boundedTorsion k (Fin n) p i hk` に prism の有界性を渡す。 |
| A3/DiscreteCase:138、A4/Perfectoidization:29–30,284–297 | π₀ の比較は `powerOperationZero_zero k p X x`。一般 k では変換の標的を φₖ に沿って制限し、素体の自己変換には `powerOperationZero_primeField p` を使う。Tot での Frobenius 比較は `powerOperationZero_eq_frobenius_tot k p X`。A 側では証明方針からの参照。 |
| A5/StrongDescent:69–84,102,263–265、A5/WeaklyInitialAndDescent:296–304 | 一般底の (g) には射の塔・余極限錐・余極限性・一様な index・各段の証人を渡す。(c) は共通始域の押し出しの対角辺。両端を一変数から n 重にテンソルする場合は `isDescendableOver_tensorMaps` を反復し、完備版 (h) と接続する。降下は `isDescendableOver_pushout A Q hQ hf` と `isDescendableOver_tot_equiv A f hf d`（`d : AmitsurData A f`）。公開される Lemma 8.6 には index の数値を追加していない。 |

このほかに、今回変更した旧名を A 側から直接呼び出す箇所は見つからなかった。`totEInfinity` と `cohomologyEquivHomology` の既存の呼び出しは名前・引数を保っている。

### 設計の訂正と未実装箇所

* **D5-03**（`003d31296`）　k = Fₚ[t] の Frobenius は k 線形ではない。一般形の終域を `cAlgForgetDerived k ≫ derivedInfinityRestrictScalars (frobenius k p)` とした。k = Fₚ では `ZMod.frobenius_zmod` と `derivedInfinityRestrictScalars_id` で自己変換に戻る。
* **D5-04**（`b5600c32f`）　記録用の `isDescendable_of_faithfullyFlat` は `Module.FaithfullyFlat A B` と `Algebra.FinitePresentation A B` の両方を仮定した。忠実平坦だけの場合には反例がある。[Aoki, *On cohomology of locally profinite sets*](https://arxiv.org/abs/2411.05995)
* **D5-05**（`459368197`・`6aef245a4`）　Mathlib の `AlgebraicTopology.alternatingCofaceMapComplex C` を使用した。`cohomologyEquivHomology` の忘却は CommRingCat → RingCat → AddCommGrpCat の合成。A0/CechAlexander:259（説明）、A1/HodgeTateMap:74、A1/CrystallineInput:179,234,237 に同じ旧名が残る。これらは A 側の中身の段階で修正する。
* **結論 True の五宣言**　`totEInfinity_cohomologyRing` は E∞ 代数の全次数の π_* の積の入口待ち。`hasDescentIndexLEOver_two_of_rhom` と `hasDescentIndexLE_two_of_rhom` はそれぞれ Mod_R と D(A) の内部 Hom 待ち。`isDescendableOver_complete` と `isDescendable_complete` は完備反射に先立つ導来テンソルの ∞ 関手（β5）待ち。`IsThickTensorIdeal.tensor` の一欄も同じ理由で残した。
* **要確認**　新たな仮名はない。正規化余鎖の Barratt–Eccles 作用（CosimplicialEInfinity）と、P⁰ を定める E(p) の作用（EInfinityPowerOperation）は本体実装時に照合する。既存の `exists_unique_dgHom.hlin` は DeRhamPolynomial の仮定の仮置きで、入口表 §1.6 に従い中身の段階に残した。
* **検査**　コメントを除いた宣言の結論を数え、Shared は 5 件、Sheaves は 11 件、drafts 全体は **16 件**。五宣言・構造体一欄の docstring に理由があること、追加した import のパス、括弧、A 側からの参照、`git diff --check` を点検した。ビルド・Lean の型検査は行っていない。
