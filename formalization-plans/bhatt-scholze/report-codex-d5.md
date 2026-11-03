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

## 第 3 部　停止点 3・Sheaves

開始基準は停止点 2 の検収 `ee7fa9fad`。Sheaves の名前つき宣言で結論が `True` だった **11 件すべて**を具体化した。加えて `derivedGlobalSections_of_le` の存在文の中の `True` を可逆性に替え、S1 の二つの層判定を新設した。

| ファイル | 開始時の 11 件の内訳 | 主張・指定した射 |
| --- | ---: | --- |
| SheafCondition | 0 | S1-E は `FinitaryExtensive` の下で、空族を含む有限積の指定錐を送ったものが極限錐になることと同値。`isSheaf_sup_iff` は二位相それぞれの層条件との同値。 |
| GlobalSections | 1 | `sheafifyUnit_isEquivalence_of_isSheaf` は実際の単位ホモトピーを ihom の辺にして `IsInvertibleEdge` を課す。`derivedGlobalSections_of_le` は二つの Γ の頂点を結ぶ **E の辺**に同じ述語を課す。 |
| CechConerveLimit | 1 | `isLimitCone_iff_restrict_cech_large` は同じ錐とその Čech 制限を比較する。A5 のように制限先の錐だけが与えられる場合は、その頂点を保つ延長の存在も別に述べた。 |
| CAlgValued | 3 | `forget_conservative` は忘却した辺の可逆性を反映する。`forget_sheafify` は各 F での `FunctorIso`、`forget_derivedGlobalSections` は `VertexIso`。忘却による極限保存には実体の `cAlgForgetDerived_mapJoinCone_isLimit` を使える。 |
| SpaceValued | 6 | `sheafification_exists_spaces`、`sheafify_discrete_eq`、`localEquiv_of_sheafifyIso`、`discretePushout_isDiscrete`、`sectionsOf_pushout`、`sectionsOf_colimit`。集合値の射を層化した辺、また押し出しの二つの合成二単体まで指定した。 |

**新設宣言（ファイル別）**

* SheafCondition — `PreservesFiniteProductsOnSite`、`isSheaf_extensive_iff_preservesFiniteProducts`、`isSheaf_sup_iff`。既存の `JoinCone.ulift` は Core/UniverseLimits の宣言につないだ。`Coverage` の既存の射影名を Mathlib の `coverings` に合わせた。
* GlobalSections — `sheafificationFunctor`。`Sheafification J E` は反射データの存在を表す Prop。証人を一つ選び、同じ反射を `sheafify` の値・単位・射に使う。
* CechConerveLimit — `PresheafLarge`、`cechShapeLarge`、`exists_limitCone_of_cech_large`。対象が Type (u+1)、射が Type u の圏の nerve はそのまま。Δ の nerve だけを持ち上げる。
* CAlgValued — 既存名を保ち、三宣言の結果を具体化した。
* SpaceValued — `setsToKan`、`discretePresheaf`、`discretePresheafInclusion`、`Is0Truncated`、`discretePushoutSquare`、`liftedSetYoneda`、`oppositeSpaceYoneda`、`weightedSectionsData`、`weightedSections`、`weightedSections_discrete`、`weightedSections_discrete_map`。重み付き切断は O の反対 Yoneda に沿う右 Kan 拡張。集合値の重みについて、従来の `sectionsOf` の選んだ極限との同型と、射 `sectionsOf_map` に関する可換式を置いた。

**A 側の呼び出しと引数**（行番号は `ee7fa9fad`）

| A 側 | 使う入口 |
| --- | --- |
| A6/ArcSite:272–288,303–332、A6/ArcSheafProperty:508–514 | `isSheaf_extensive_iff_preservesFiniteProducts F` は site に `FinitaryExtensive` を要求する。`isSheaf_sup_iff J J' F` は `arcTopology_eq_sup` の後に適用する。A6 の `PreservesFiniteRingProducts` は反対圏の有限余積を環の有限積に戻した特殊化。適用時には、異なる二射影の affine 側の引き戻しが零環であることを示す。零環は site の対象であり、空被覆の条件も含む。A6 の古い docstring の修正は中身の段階。 |
| A5/WeaklyInitialAndDescent:120–141,177–180 | `isLimitCone_iff_restrict_cech_large hU d F c`。A5 の `limit_perfUnder_eq_tot` の入力は小さい Δ 側の錐 t と極限性 ht なので、ここでは `exists_limitCone_of_cech_large hU d F t ht` を使う。A5 の `unopUnop` による添字の読み替えと合わせる。 |
| A0/CechAlexander:227–240、A2/DerivedPrismaticCohomology:125–140,288–292、A5/PerfectSiteComparison:65–78、A6/ArcSheafProperty:564 | `sheafifyUnit_isEquivalence_of_isSheaf J hJ hF` は S2 が Γ の錐を前層へ移す入口。粗い位相との比較は `derivedGlobalSections_of_le J J' h hJ hJ' hE hF`。`derivedGlobalSectionsCAlg J A hJ hA F` の引数は同じ。A2 の `forget_derivedGlobalSections J A hJ hJ' hA hD F` は `forget_sheafify J A hJ hJ' F` と極限保存から。 |
| A5/InterfaceLimitCone:62 | `forget_isLimitCone A c hc` の極限保存。`forget_conservative A e he` は対象を推論し、忘却後の辺の可逆性を受け取る。 |
| A6/Excision:144,186–199,208–209,261–286 | 既存の `sectionsOf_eq_limit_elements`・`sections_localEquiv_iso` の直接呼び出しは同じ引数順。`localEquiv_of_sheafifyIso J hJ φ hφ` は離散な φ を同じ層化関手で送った ihom の辺の可逆性。`discretePushout_isDiscrete f g` と `sectionsOf_pushout f g O hE` では商から来る脚に `Mono f` を供給し、標準余錐の全体を反転して切断を取る。`sectionsOf_colimit O hE c hc` は空間値前層圏での小さい ∞ 余極限錐を受け取る。 |

**入口表との差**　D5-06（`4254d57c8`）で S1-E の非交叉性を明示した。D5-07（`109a2cde4`）について、`SpaceInfinity` とその `Quasicategory` インスタンスは F1/Categories/CatInfinity に既存。さらに現行の F2/Presentable/SpacePresentable には `space_isPresentable : IsPresentable SpaceInfinity`（`751f1bfba`）もある。S8-1 の引数をこの定理で満たせる。集合値の押し出しに絞った S8-4 には A6 が持つ単射の仮定を明記した。一般の集合の余等化子には適用しない。例えば二本の恒等写像を点から点へ送る図式のホモトピー余等化子は円になる。

## BS-D5 総括

| 区分 | 開始時の結論 `True` | 具体化 | 残り |
| --- | ---: | ---: | ---: |
| DerivedGeneral | 14 | 14 | 0 |
| Shared | 28 | 23 | 5 |
| Sheaves | 11 | 11 | 0 |
| **合計** | **53** | **48** | **5** |

宣言を分割しても開始時の一件として数えた。この表とは別に、Shared/Descendable の `finiteColimits`・`retracts`・`shifts` の三欄と、Sheaves/GlobalSections の `derivedGlobalSections_of_le` の結論中の存在条件を具体化した。全新設名は第 1 部「定義と新設した入口」、第 2 部「型を付けた宣言・新設した入口」、本部「新設宣言」にファイル別で列挙した。A 側の来歴・引数・実コードの参照箇所は各部の対応表にあり、A0〜A9 の編集はない。

**× のまま残した五宣言と一欄**

| ファイル | 宣言・欄 | 待っているもの |
| --- | --- | --- |
| Shared/CosimplicialEInfinity | `totEInfinity_cohomologyRing` | 全次数の E∞ ホモトピー環の積と cup 積の比較。π₀ の環だけでは型が決まらない。 |
| Shared/Descendable | `hasDescentIndexLEOver_two_of_rhom`、`hasDescentIndexLE_two_of_rhom` | 一般の底の Mod_R、離散底の D(A) の内部 Hom の ∞ 関手。 |
| Shared/Descendable | `isDescendableOver_complete`、`isDescendable_complete` | 導来テンソルの ∞ 関手（β5）と反射を合成した完備テンソル。 |
| Shared/Descendable | `IsThickTensorIdeal.tensor`（欄） | 任意の頂点との導来テンソルの ∞ 関手。 |

**要確認の一覧**

* **DerivedGeneral**　新規の未確定名はない。M13・M13-CAlg に証明と実装が残る。
* **Shared**　CosimplicialCupProduct の加法群への忘却は D5-05 の RingCat 経由で接続。CosimplicialEInfinity の正規化余鎖に対する Barratt–Eccles 作用、EInfinityPowerOperation の E(p) による P⁰ は実装時の要確認。DeRhamPolynomial の `exists_unique_dgHom.hlin` は η¹ の線形性を表す未具体化の **仮定**。上表の残り五宣言には数えていない。
* **Sheaves**　SpaceValued の `discretePresheaf`・`Is0Truncated` の公開名と離散埋め込みの接続を ∞ レーンで照合する。presentable 性の現行名は上記の `F2.Presentable.space_isPresentable`。S1 の生成系からの降下、CAlgValued の忘却の同値反映と非安定な S4、S8 の右 Kan 拡張・層化の比較は証明段階の入口。CAlg の忘却の極限保存は `FreeProbeDerivedFreeForget` に無条件版があった。
* **設計訂正**　完備化・切り捨てでは D5-01・02、Shared では D5-03〜05、Sheaves では D5-06・07 を反映した。設計書・入口表の他セッションのコミットには変更を加えていない。

**確認の範囲**　開始基準 `dc77a84dd` と現状をコメントを除いて照合した。Sheaves の `True` 結論と `∃ e, True` は解消し、drafts 全体に残る `True` 結論は上表の Shared 五宣言だけである。実 import 先、新設・変更した宣言名、括弧、変更先と `git diff --check` を静的に確認した。ビルド・Lean の型検査は実行していない。
