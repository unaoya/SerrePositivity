# 基盤の入口表：drafts が仮定する基盤側の宣言と、その担当・時期

作成：2026-11-03（BS 作業チャット、BS-D4 完了後）。正本はこのファイル。関連：`design-status.md` §4 の 7・8、`infinity-sheaves-design.md` §4・§8・§13、
`../infinity-foundation-plan.md` の M12〜M15、Codex の報告 `report-codex-d1.md`〜`d4.md` の「接続する入口」の表。

## 0. 目的と使い方

A0〜A9 の drafts（51 本）には、結論が `True` の仮置きが残っていない（BS-D4、main fea4346d6）。残る仮置きは基盤側（`drafts/Shared/`・`drafts/Sheaves/`・
`drafts/DerivedGeneral/`）の 53 件と、A 側の `-- 要確認：〜へ` の注記（約 40 箇所）で、どれも「基盤のどの宣言を待っているか」を指している。
この表はそれを一枚にまとめたもので、三つの用途に使う。

1. **BS-D5**（基盤側の仮置きの型付け、`bhatt-scholze-codex-d5.md`）の対象と形の指定。
2. **∞ レーンへの依頼文**の本体（W2b の取り込み後に調整役が起こす。§4）。
3. **段 2 の点検表**：中身を書くとき、どの基盤の宣言が入れば A のどの単位が動くか（§5）。

凡例（単位と担当は `../infinity-foundation-plan.md` M12〜M15 と `design-status.md` §4 の 7 の分担）：

| 記号 | 内容 | 担当 | 置き場所 |
| --- | --- | --- | --- |
| S1〜S3、S6、S8 | ∞ 層の一般論のうち既存の基盤で書ける部分（層条件、Γ・RΓ の型、弱終対象の Čech 脈体、切り落とし、空間値の層） | BS（M12a・M12e、W2b 後の段 G） | `InfinityCategories/Sheaves/` |
| S4・S5 | 層化の存在・完全性 | **BS**（調整役回答 11-03、coordination.md 8ef332d45。G4・G6・G8・G7 は ∞ が供給） | `InfinityCategories/Sheaves/` |
| G3・G12・G13 | D(A)・CAlg_A・𝒮 の presentable 性 | ∞ レーン（M12c。G12 は EInfinity 側。𝒮 の名前の候補 `SpaceInfinity`、`IsPresentable 𝒮` は F2/） | `Derived/`・`EInfinity/`・`Kan/` |
| G4・G6・G8・G9 | 関手圏の presentable 性、局所置換、空間とのテンソル、効果的エピの Čech 脈体 | ∞ レーン（M12b・M12d） | `F2/Presentable/`・`HomotopyLimits/` |
| M13 | D(A) の t 構造・切り捨て、導来 (p,d) 完備化、係数制限 f_*（D 版） | BS（W2b 後の段 G） | `InfinityCategories/Derived/` |
| M13-CAlg | 係数制限・係数拡大・完備反射の CAlg 版 | BS（置き場所は調整役） | `EInfinity/` |
| M14 | E∞-F_p 代数の冪作用 P⁰ | 未定（A4 の中身の段階） | `EInfinity/PowerOperation/` |
| M15 | Mathew の descendability（Mod_R の thick ⊗-ideal） | 未定（A5 の中身の段階） | `EInfinity/Descendable/` |
| Shared | 余単体的 cup 積・Bockstein、多項式の de Rham 複体、Tot_{E∞} | BS（2b の後） | `HomologicalAlgebra/Cosimplicial/`・`CommutativeAlgebra/DeRham/`・`EInfinity/` |

「D5」欄：○＝BS-D5 で具体的な型にできる、△＝仮の名前（`-- 要確認`）を置けば型にできる、×＝基盤の概念そのものが未定で型にできない（`True` のまま残し、理由を書く）。

## 1. 表 A：基盤側の宣言（残る `True` 53 件と、型つきだが本体が基盤待ちの定義）

### 1.1 DerivedGeneral/CompletionFunctor（M13、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `IsDerivedComplete`・`completeSubcomplex`（型つき sorry） | D(A) の (p,d) 完備な頂点と充満部分複体 | A2 `completeAt`・`prismComplete`（A2 が独自に定義）、A1 `CompleteModules`、A4 `CompleteCAlg` | ○ | A2 の `completeAt (a : A)`（`IsComplete A a` を同値で引き戻す）を基盤に置き、`IsDerivedComplete (s : Finset A) x := ∀ a ∈ s, completeAt a x`、`completeSubcomplex s := fullSubcomplexOnVertices _ (IsDerivedComplete s)` |
| `completion_isReflective` | 完備化は包含の左随伴 | A1 `moduleReflection`（s = {p, d}）、A2 `pCompletionReflection`（s = {p}）、A4 の塔の完備化、`derivedInfinityRestrictScalars_completion` | ○ | `completionReflection s : Σ L : derivedInfinityCategory A ⟶ (completeSubcomplex s : SSet), QCatAdjunction L (completeSubcomplex s).ι`、`completion s := L ≫ ι`（A 側は `completion` を参照していないので引数を足してよい） |
| CAlg 版（新設、G-A2-3・9） | (p,d) 完備な E∞ 代数への反射 | A1 `primeAlgReflection`（{p}）、A2 `prismCompleteReflection`（{p,d}）、A4 `reflectCompleteCAlg`、A5 `completePiZeroReflection` の始域 | ○ | `cAlgCompleteSubcomplex s := fullSubcomplexOnVertices (CAlg_R A) (fun X => IsDerivedComplete s ((cAlgForgetDerived A).app _ X))`、`cAlgCompletionReflection s : Σ L, QCatAdjunction L ι`、`cAlgCompletion s`。対称モノイダル性の証明は段 G |
| `completion_tensor_koszul` | X^∧ ⊗ Kos(s^n) ≃ X ⊗ Kos(s^n) | A0-3c（完全平坦性の移送）、`derived_nakayama` | ○ | semifree 代表 `(dgNerve.vertexEquiv A (Semifree A) x).val` 上の `koszulComplexOn` で、単位 x → x^∧ が各次数のホモロジーに同型を誘導（A1 `HasFiniteCompleteTorAmplitude` と同じ流儀。⊗^L の ∞ 関手を待たない） |
| `completion_exact` | 完備化は fiber 列を保つ | A2 HT filtration、Lemma 4.22 | ○ | `Derived.StableLimits` の fiber 四角形の述語で「`completion s` は pullback 四角形を保つ」 |
| `complete_colimit` | 完備圏の余極限 ＝ 余極限の完備化 | A2-2 sifted、A4 Frobenius 余極限 | ○ | `IsColimitCone c → IsColimitCone (mapJoinCocone (completionReflection s).1 c)`（左随伴は余極限を保つ） |
| `completedBaseChange`（def、本体 `True`） | (− ⊗^L_A B)^∧ と prism の射に沿う関手性 | A2 `completedPrismBaseChange`、Lemma 4.20・4.22、Construction 6.1 | ○ | `completedBaseChange (f : A →+* B) (s : Finset A) := derivedInfinityBaseChange f ≫ completion B (s.image f)`。**A2 がこの名前を参照している**ので、引数を決める前に A2 の呼び出しを確認する |

### 1.2 DerivedGeneral/Truncation（M13、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `truncationLE_counit`（def、`True`） | τ^{≤n} → id と H^i（i ≤ n）での同型 | A2 `hodgeTateFiltration_step`（A2:139） | ○ | `truncationLE_counit n : FunctorHom (truncationLE A n) (𝟙 _)`、`truncationLE_counit_h n x (i ≤ n) : IsIso (H A i の成分)`。追加 `truncationLE_step n : FunctorHom (truncationLE A n) (truncationLE A (n+1))`（増大列。A2:139 が待つ） |
| `truncation_cofiber` | τ^{≤n−1}X → τ^{≤n}X → H^n(X)[−n] | A2 gr^i = Ω^i[−i] | ○ | cofiber 四角形の述語（Stable）で、第三項は離散加群 `ModuleCat.of A (H A n x)` を D(A) に入れたものに `loopFunctor`／`suspensionFunctor` を n 回。**D5-02**：`discreteEmbedding A` の始域は A 代数（`nerve (Under (CommRingCat.of A))`）なので加群には使えない。A2 `ordinaryFormsDiagram` と同じく `moduleSemifreeResolutionFunctor A ⋙ …` と `closedNerveInclusion A (Semifree A)` で入れる。再利用のため `discreteModuleEmbedding A : nerve (ModuleCat A) ⟶ derivedInfinityCategory A := nerveMap (moduleSemifreeResolutionFunctor A) ≫ closedNerveInclusion A (Semifree A)` を DerivedGeneral に一つ置く（`discreteEmbedding` 自体が `discreteAlgebraModule ⋙ moduleSemifreeResolutionFunctor` を経由しているので、その加群から先の部分） |
| `tStructure_axioms` | HA 1.2.1.4 | 導来 Nakayama、HT filtration の一意性 | ○ | 三つに分ける：直交性（D^{≤n} と D^{≥n+1} の間の写像空間の π₀ が自明。F1B の `QCatAdjunction.hoVertexHomEquiv` と同じ ho 圏の Hom）、shift（Σ = [1] は既存の `derivedSuspensionShiftObjectIso`。cohomological 添字なので H^i(Σx) = H^{i+1}(x)、よって **`IsConnectiveAt n x ↔ IsConnectiveAt (n-1) (Σx)`**。D5-01 で訂正：以前の (n+1) は X = A[−1]、n = 0 が反例）、分解（標準の τ^{≤n}x → x → τ^{≥n+1}x が cofiber 四角形、安定なので同時に fiber 四角形。`truncationGE (n+1)` を使う） |
| `truncationLE_of_isConnective` | X ∈ D^{≤n} ⇒ τ^{≤n}X ≃ X | A2 `hodgeTatePoly_bounded` | ○ | `IsConnectiveAt n x → IsInvertibleEdge ((truncationLE_counit n).成分 x)` |
| `derived_nakayama` | 完備 X で X ⊗^L A/(p,d) = 0 ⇒ X = 0 | A1（Thm 5.2 の η、Constr 6.1 (1)、Cor 4.12）、A2 D32、A5 StrongDescent・SemiperfectoidCase | ○ | `IsDerivedComplete {p,d} x → (∀ i, IsZero ((koszulComplexOn ![p,d] M).homology i)) → ∀ i, Subsingleton (H A i x)`（M は semifree 代表。⊗^L を待たない） |

### 1.3 DerivedGeneral/ScalarRestriction（M13 の D 版、CAlg 版は EInfinity 側）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `derivedInfinityRestrictScalars`（型つき sorry） | f_* : D(T) → D(S) | A0 `prismaticCohomologyFrobenius`、A1、A2 HT、A8 AlmostConnectivity | — | 本体は M13 |
| `derivedInfinityBaseChange_restrictScalars_adjunction` | f^* ⊣ f_* | A4 の塔（φ 半線形射の読み替え） | ○ | `QCatAdjunction (derivedInfinityBaseChange f) (derivedInfinityRestrictScalars f)`（F1B の `QCatAdjunction`、A2 の反射と同じ型） |
| `cAlgRestrictScalars`・`cAlgBaseChange`（型つき sorry） | CAlg の係数制限・係数拡大 | 10 ファイル（A2〜A7） | — | 本体は M13-CAlg |
| `cAlgBaseChange_restrictScalars_adjunction` | f^! ⊣ f_* | A2 `perfectBaseComparison`（単位 `.unitHom`）、A5 StrongDescent `prismScalarExtension` | ○ | `QCatAdjunction (cAlgBaseChange f) (cAlgRestrictScalars f)` |
| `derivedInfinityRestrictScalars_completion` | 完備化と f_* の両立 | A4 `restrictFrobeniusCompletion` | ○ | `(I : Finset S) (J : Finset T) (h : (Ideal.span (f '' I)).radical = (Ideal.span (J : Set T)).radical) : FunctorIso (completion T J ≫ derivedInfinityRestrictScalars f) (derivedInfinityRestrictScalars f ≫ completion S I)` |
| `cAlgRestrictScalars_h0` | f_* と H⁰ の両立 | A4 `restrictH0Equiv`・`restrictH0Equiv_base`、Lemma 8.4 (b)、E3 の `h0` | ○ | 基盤に `cAlgH0Ring (x : (CAlg_R S) _⦋0⦌) : Type u`＋`CommRing`＋`Algebra S` を新設し、`cAlgH0Ring ((cAlgRestrictScalars f).app _ x) ≃+* cAlgH0Ring x`（S 作用は f に沿う）。A4 の `cAlgH0Algebra`（A4・A5・A7・A8 の 6 本が参照）は中身の段階でこれに置き換える |
| 型つき（参考）：`cAlgRestrictScalars_isColimitCone`（sifted のみ、D2-01）、`_of_bijective`、`derivedInfinityRestrictScalars_isColimitCone`、`cAlgRestrictScalars_algebraEmbedding`（D3-03、A5 `discreteRestrictionIso`） | | | — | 本体は M13 |

### 1.4 Shared/CosimplicialBockstein（HA/Cosimplicial、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| `bockstein_leibniz` | β(a ∪ b) = β a ∪ b + (−1)^{|a|} a ∪ β b | A1 HodgeTateMap（η^* が dg 射） | ○ | `cohomologyEquivHomology` で `regularBockstein` を `Cosimplicial.cohomology` に移してから、`cup` について述べる（D4-03） |
| `bockstein_natural` | d を d′ に写す射で β は自然 | A1 HodgeTateMap（参照あり） | ○ | `(g : C ⟶ C') (hg : ∀ n, g.app n (d n) = d' n)` について `cohomologyMap g` と β の可換 |

### 1.5 Shared/CosimplicialEInfinity（EInfinity の上、担当は BS 提案）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `totEInfinity`（型つき sorry） | Tot_{E∞}(X^•) | A1 CrystallineInput・DeRhamComparisonPoly、A2 DerivedPrismaticCohomology | ○ | **関手形**にする：`totEInfinityFunctor : nerve (CosimplicialAlgebra A) ⟶ CAlg_R A`（どちらも `SSet.{u+1}`、ulift 不要）、`totEInfinity X := totEInfinityFunctor.app _ (nerveVertex X)`（名前は保つ） |
| `totEInfinity_map`（def、`True`） | 射 X → Y の Tot_{E∞} | A1 `pdTotMap` | ○ | 関手の辺 `SSet.Edge (totEInfinity A X) (totEInfinity A Y)` |
| `totEInfinity_forget` | 下の複体は交代余面複体 | A0 の D(A) 値 Tot との一致 | ○ | 各 i で `H A i ((cAlgForgetDerived A).app _ (totEInfinity A X)) ≃ₗ[A] Cosimplicial.cohomology (X ⋙ forget) i`（添字の向きは Truncation の規約に合わせる） |
| `totEInfinity_isLimitCone` | Tot_{E∞} は CAlg_A での Δ 上の極限 | A2 `prismaticCohomologyCAlg_eq_totEInfinity` | ○ | `totEInfinityCone X : JoinCone (X の nerve 図式 ≫ algebraEmbedding A)` と `IsLimitCone` |
| `derivedGlobalSectionsCAlg_eq_totEInfinity` | 脚注 10 の CAlg 版 | A2 | ○ | S3 `CechNerveData`・`IsWeaklyTerminal` と `ringPresheafToCAlg` で `VertexIso` |
| `totEInfinity_cohomologyRing` | H^* の環構造 ＝ cup 積 | A1 D27 | × | E∞ 代数のホモトピー環 π_* の基盤名が要る（M14 の `homotopy` と合わせて段 G）。`True` のまま理由を書く |

### 1.6 Shared/DeRhamPolynomial（CA/DeRham、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| `completedForms_eq_derivedCompletion_of_boundedTorsion` | 有界 p 冪ねじれの k で LΛ_p(Ω^i) は離散で Ω̂^i | A1-1・A1-3、A2 `hodgeTatePoly_gr`・`polyForms_boundedComparison` | ○ | `(hk : k の p 冪ねじれが有界) : VertexIso ((completion k {p}).app _ ((discreteModuleEmbedding k).app _ (ModuleCat.of k (forms k T i)))) ((discreteModuleEmbedding k).app _ (ModuleCat.of k (completedForms k T p i)))`（加群の埋め込みは D5-02 の `discreteModuleEmbedding`。`discreteEmbedding k` は代数用）（有界性の述語は `IsBoundedPrism` が使っている既存名を grep） |
| 型つき残り：`completedForms` の本体、`exists_unique_dgHom` の仮定 `hlin` | | | — | 中身の段階 |

### 1.7 Shared/Descendable（M15、段 G）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `IsDescendableOver`・`HasDescentIndexLEOver`（型つき sorry） | Mod_R(D(A)) の thick ⊗-ideal | A5 StrongDescent | — | 本体は M15 |
| `IsThickTensorIdeal` の四欄・`IsDescendable` の本体 | D(A) の thick ⊗-ideal | 以下すべて | × | **D(A) の導来テンソル ⊗^L の ∞ 関手がない**（§4 の 8）。四欄のうち `finiteColimits`・`retracts`・`shifts` は型にできる（`IsColimitCone`・retract の辺・`suspensionFunctor`）、`tensor` だけ `True` |
| `isDescendableOver_unit_iff` | 離散環版との一致 | — | ○ | R = `(algebraEmbedding A).app _ (nerveVertex (Under.mk (𝟙 _)))`、f = B の構造射 |
| `isDescendableOver_pushout`・`_comp`・`_tensor`、`isDescendable_baseChange`・`_comp`・`_tensor` | (a)(b)(c) | A5-4 の降下 | ○ | 押し出し・テンソルは CAlg_R A の余極限錐（`JoinCocone`＋`IsColimitCone`、span 形）で述べる。合成は quasicategory の合成の証人（2 単体） |
| `isDescendableOver_tot_equiv`・`isDescendable_tot_equiv` | (e) M ≃ Tot(M ⊗ B^{⊗•+1}) | A5 WeaklyInitialAndDescent（M = R の場合だけ） | ○ | `structure AmitsurData (f : SSet.Edge R B)`（nerve Δ 上の余単体的図式、R からの増大錐、第 0 頂点 ≃ B、各頂点が反復押し出しであることの証人）を置き、`IsDescendableOver A R B f → (d : AmitsurData f) → IsLimitCone d.aug` |
| `hasDescentIndexLEOver_two_of_rhom`・`hasDescentIndexLE_two_of_rhom` | (f) RHom(F^{⊗2}, R) ∈ D^{<0} ⇒ index ≤ 2 | A5 `fiberSquareRHom`（Lemma 8.6 の n = 1） | × | Mod_R の内部 Hom／D(A) の RHom の ∞ 関手がない。`True` のまま |
| `hasDescentIndexLEOver_frobeniusColimit`・`hasDescentIndexLE_frobeniusColimit` | (g) BS17 Lemma 11.22 | Lemma 8.6 の perf 版 | ○ | ℕ の nerve 上の図式と余極限錐（A4 `frobeniusTower` と同じ形）、各段で index ≤ n ⇒ 余極限で ≤ 2n |
| `isDescendableOver_complete`・`isDescendable_complete` | (h) 完備版 | Lemma 8.6 の形 | × | 完備テンソル（⊗^L の後に `completion`）が ⊗^L 待ち。`True` のまま |
| `isDescendable_of_faithfullyFlat` | 忠実平坦**かつ有限表示** ⇒ descendable（[Mat16, Prop 3.31]） | 記録 | ○ | **D5-04**：忠実平坦だけでは descendable とは限らない（Aoki, arXiv:2411.05995 の反例）。離散 A 代数 B が忠実平坦かつ有限表示（`Module.FaithfullyFlat` ＋ `Algebra.FinitePresentation`）の場合に限定し、`algebraEmbedding` で埋め込んで述べる |

### 1.8 Shared/EInfinityPowerOperation（M14、段 G）

| 宣言 | 主張 | 使う側 | D5 | D5 での形（推奨） |
| --- | --- | --- | --- | --- |
| `homotopy`・`powerOperationZero`（型つき sorry） | π_n と P⁰ | A3 G-A3-9、A4 Lemma 8.4 | — | 本体は M14 |
| `powerOperationZero_zero` | π_0 で Frobenius | Lemma 8.4 (b) | ○ | `homotopy k p X 0 ≃+* cAlgH0Ring X`（1.3 の新設）を置き、`P⁰ x = x ^ p` |
| `powerOperationZero_natural` | E∞ 射で自然 | Δ_perf/p の Frobenius | ○ | `homotopyMap (f : SSet.Edge X Y) n : homotopy X n →+ homotopy Y n` を追加し、P⁰ との可換 |
| `powerOperationZero_natTrans`（def、`True`） | U 上の coherent な自然変換（**φ_k 半線形**） | (iii) | ○ | **D5-03**：P⁰ は k 線形ではなく Frobenius 半線形（k = F_p[t]、B = k で t ↦ t^p は k 線形でない）ので、D(k) 値の自己変換 U ⇒ U は誤り。一般形は `FunctorHom (cAlgForgetDerived k) (cAlgForgetDerived k ≫ derivedInfinityRestrictScalars (frobenius k p))`（U(X) → φ_{k*} U(X)、W9-II-02 の強さ）。k = F_p では `frobenius = RingHom.id` と `derivedInfinityRestrictScalars_id` で自己変換に特殊化。`powerOperationZero` はその成分が π_n に誘導する写像 |
| `powerOperationZero_eq_frobenius_tot` | 離散 B で P⁰ = U(Frob)、Tot へ移る | Lemma 8.4 (a) | ○ | 離散 B（CharP B p）の `algebraEmbedding` での成分が Frobenius の辺（φ_k 半線形なので k 代数の射 B → φ_{k*}B として読む、D5-03）の U 像とホモトピック；`totEInfinity` への移送は `totEInfinity_isLimitCone` と自然変換の錐との両立 |

### 1.9 Sheaves/SheafCondition・GlobalSections（S1・S2、M12a、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| S1-E `isSheaf_extensive_iff_preservesFiniteProducts`（今は A6/ArcSite に仮置き） | extensive coverage の層 ⇔ 有限積を保つ（**`FinitaryExtensive`**、D5-06） | A6 `isSheaf_arc_iff_cech` | ○ | SheafCondition へ移す（A6 側は中身の段階で差し替え。A6 の docstring の `FinitaryPreExtensive` は誤りで、非交叉性＝二つの射影の引き戻しが零環であることを A6 の site で示す）。`isSheaf_sup_iff`（J ⊔ J′ の層 ⇔ 両方の層、A6 `arcTopology_eq_sup`）も新設 |
| `Sheafification J E : Prop`（`sheafify`・`sheafifyUnit` は型つき） | 層化の存在 | A0・A2・A5・A6（仮定として受け取る） | — | S4：G4・G6・G8 の後、**担当未定**（§4 の 9） |
| `sheafifyUnit_isEquivalence_of_isSheaf` | 層の単位は同値 | Cor 3.12、RΓ(O_Δ) = Γ(O_Δ) | ○ | ihom の辺に `IsInvertibleEdge`（W9-I-03 の規約） |
| `derivedGlobalSections_of_le`（∃ e, `True`） | 位相を粗くしても RΓ は同じ | Rem 4.5、Prop 8.5 | ○ | `∃ e, IsInvertibleEdge e` |
| `derivedGlobalSections`（型つき、`hE : IsPresentable E`） | RΓ := Γ(F^♯) | A0・A2・A3・A5・A6 | — | E = D(A) なら G3、E = CAlg_A なら G12 が仮定を満たす |

### 1.10 Sheaves/CechConerveLimit（S3、M12a、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| `isLimitCone_iff_restrict_cech`（小、型つき sorry） | 弱終対象の Čech 脈体への制限で極限判定 | A0 CechAlexander、A5、A6 | — | 証明は G8／G9・G10 |
| `isLimitCone_iff_restrict_cech_large` | 大きい添字圏の版（D3-02） | A5 `limit_perfUnder_eq_tot` | ○ | `PresheafLarge (𝒟 : Type (u+1)) [Category.{u} 𝒟] E := nerve 𝒟ᵒᵖ ⟶ E`（`SSet.{u+1}` なので ulift 不要）で小さい版を写す |

### 1.11 Sheaves/CAlgValued（S4 の CAlg 版、M12a／EInfinity）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| `forget_conservative` | U は保存的 | 極限錐の反映 | ○ | `IsInvertibleEdge ((cAlgForgetDerived A).map e) → IsInvertibleEdge e`（辺の写像の既存名を grep） |
| `sheafification_exists_cAlg (hA : IsPresentable (CAlg_R A))`（型つき sorry） | CAlg 値の層化 | A2 `prismaticCohomologyCAlg`、A5 | — | G12 ＋ S4 の非安定版 |
| `forget_sheafify` | U(F^♯) ≃ (U F)^♯ | A0 の D(A) 値 Δ と A2 の CAlg 値 Δ の一致 | ○ | 各 F で `sheafify J hJ' (forgetPresheaf (sheafify J hJ F))` と `sheafify J hJ' (forgetPresheaf F)` の `FunctorIso`（`Sheafification` は Prop なので関手としての L は使えない） |
| `forget_derivedGlobalSections` | U(RΓ_CAlg F) ≃ RΓ_{D(A)}(U ∘ F) | 同上 | ○ | `VertexIso` |

### 1.12 Sheaves/SpaceValued（S8、M12e、BS）

| 宣言 | 主張 | 使う側 | D5 | D5 での形 |
| --- | --- | --- | --- | --- |
| E = 𝒮 | 空間の ∞ 圏 𝒮 は**既にある**（D5-07 で訂正）：`SpaceInfinity : SSet.{u+1} := SimplicialNerve KanObject`、`instance spaceInfinity_quasicategory`（`InfinityCategories/F1/Categories/CatInfinity.lean`、Kerodon 3.1.6.1） | S8 全体、A6 Cor 8.12 | ○ | 実体を参照する。`IsPresentable SpaceInfinity` も F2 の `space_isPresentable`（F2/Presentable/SpacePresentable）として既にある（BS-D5 第 3 部）。残る要確認は離散前層の接続（`Type u` → 𝒮 の離散埋め込み、drafts の `setsToKan`・`discretePresheaf`・`Is0Truncated` の公開名）だけ |
| `sheafification_exists_spaces` | S8-1 | Cor 8.12 | △ | `IsPresentable SpaceInfinity → Sheafification J SpaceInfinity` |
| `sheafify_discrete_eq` | 離散な前層の層化は 1 圏の層化 | 局所同値の判定 | △ | `discretePresheaf : (𝒞ᵒᵖ ⥤ Type u) → Presheaf 𝒞 SpaceInfinity`（仮置き）と `FunctorIso (sheafify J hJ (discretePresheaf P)) (discretePresheaf ((presheafToSheaf J _).obj P).val)` |
| `localEquiv_of_sheafifyIso` | S8-2′ | A6 `sections_localEquiv_iso` の証明 | △ | `IsLocalEquivSet J φ → IsInvertibleEdge (L(discretePresheaf φ))` |
| `discretePushout_isDiscrete` | S8-3 | A6 `homSheaf_pushout` | △ | `Is0Truncated`（仮置き）が単射に沿う押し出しで保たれる |
| `sectionsOf_pushout` | S8-4 の押し出し | A6 Cor 8.12 | ○ | cospan 形の `JoinCone` と `IsLimitCone` |
| `sectionsOf_colimit` | 一般の余極限（記録） | — | ○ | 述べるなら **∞ 余極限**（`Presheaf 𝒞 SpaceInfinity` の `IsColimitCone`）で。1 圏の余極限では偽（余等化子の例：円） |
| 型つき残り：`sectionsOf` の `HasLimit`（G13 の系）、`sections_localEquiv_iso`（S8-5、HTT 5.5.4.20） | | | — | 証明は段 G |

## 2. 表 B：A 側の「要確認／待ち」→ 入口

| A 側 | 待っているもの | 入口（基盤の宣言） | 状態 |
| --- | --- | --- | --- |
| A0/PrismaticEnvelope `IsCompletelyRegularRel` | Koszul ホモロジーの API | HA の `koszulComplexOn`（2b の改名後の名前） | A0 の中身の段階（D20 の式との接続） |
| A0/PrismaticSite `structurePresheafDerived` | `uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C` の比較 | Core（存在確認。なければ小補題を ∞ へ、§4 の 10） | 確認待ち |
| A0/PrismaticSite `hodgeTateCohomology` | D(A) の A/d とのテンソル | **⊗^L は不要**：f : A → A/d について `derivedInfinityRestrictScalars f ∘ derivedInfinityBaseChange f` で Δ̄ = f_* f^* Δ と書ける | 解決（A0 の中身で） |
| A0/PrismaticSite `prismaticCohomologyFrobenius` | φ_A に沿う係数制限 | `derivedInfinityRestrictScalars`（型つき） | M13 |
| A1/CrystallineInput `pdTotMap` | 余単体的射の Tot_{E∞} | `totEInfinity_map`（1.5） | D5 |
| A1/DeRhamComparisonPoly `primeAlgReflection` | 主元 p の CAlg 反射 | `cAlgCompletionReflection {p}`（1.1） | D5 |
| A1/HodgeTateComparison `moduleReflection` | (p,d) の反射 | `completionReflection {p, d}`（1.1） | D5 |
| A2/BaseChangeAndTensor `perfectBaseComparison` | f^! ⊣ f_* の単位 | `cAlgBaseChange_restrictScalars_adjunction`（1.3） | D5 |
| A2/HodgeTateFiltration `pCompletionReflection` | 主元 p の反射 | `completionReflection {p}` | D5 |
| A2/HodgeTateFiltration:139 | τ^{≤i} の増大列と余単位 | `truncationLE_step`・`truncationLE_counit`（1.2） | D5 |
| A2/HodgeTateFiltration:194 | Ω̂ と LΛ_p(Ω) の比較 | `completedForms_eq_derivedCompletion_of_boundedTorsion`（1.6） | D5 |
| A2/DerivedPrismaticCohomology `prismCompleteReflection` | CAlg の (p,d) 完備反射 | `cAlgCompletionReflection {p, d}` | D5 |
| A2/DerivedPrismaticCohomology:122、A5/PerfectSiteComparison `perfectCoefficientPresentable` | CAlg_A の presentable 性 | G12 | ∞ 依頼 |
| A2/DerivedPrismaticCohomology:156 | Tot_{E∞} の極限性 | `totEInfinity_isLimitCone` | D5 |
| A2/DerivedPrismaticCohomology:198 | site の R に関する RΓ の関手性 | A0/S2（`PolyDeltaData.map_eval`、cutoff の比較） | A0 の中身の段階 |
| A3/DiscreteCase G-A3-9 | mod p の Frobenius と P⁰ の比較 | M14 `powerOperationZero` ＋ A2 `derivedPrismaticFrobenius` | 段 G |
| A3/LciAndQuasiregular `padicBaseAlgebra` | p 完備環の標準 ℤ_p 作用 | HA/DerivedCompletion の主元完備化の単位（2b の改名後） | 2b 後 |
| A4/Perfectoidization:124・156・167 | 完備 CAlg の包含・反射・mod d | A2 `prismCompleteInclusion`・`prismCompletion`・`prismModIdeal ≫ cAlgBaseChange`（BS-D4 の対応表） | 中身の段階で置換 |
| A4/Perfectoidization:205・211・268 | 同型に沿う制限、完備化との両立、H⁰ | `cAlgRestrictScalars_isColimitCone_of_bijective`・`_comp`・`_id`、`derivedInfinityRestrictScalars_completion`、`cAlgRestrictScalars_h0`（1.3） | D5 |
| A5/PerfectSiteComparison:109・144 | 離散 Frobenius 成分、animated π₀ | A2 `discreteFrobeniusComponent`・`completePiZeroReflection`（BS-D4） | 中身の段階で置換 |
| A5/PerfectSite `discreteRestrictionIso` | 離散埋め込みと制限の比較 | `cAlgRestrictScalars_algebraEmbedding`（型つき、D3-03） | M13 |
| A5/WeaklyInitialAndDescent `limit_perfUnder_eq_tot` | S3 の大きい版 | `isLimitCone_iff_restrict_cech_large`（1.10） | D5 |
| A5/StrongDescent `fiberSquareRHom` | Mod_D の fiber・相対テンソル・内部 Hom | M15（×） | 段 G |
| A5/StrongDescent:181・193・207 | de Rham 側 | A1-5 `rootSource`・`rootFormsAugmentation`・`deRham_iso_rootAlgebra_modP`（BS-D4） | 解決 |
| A6/ArcSite S1-E（:311・318） | extensive coverage の層 ⇔ 有限積保存 | SheafCondition へ移す（1.9） | D5 |
| A6/ArcSite:422、A6/PerfectoidFiniteProduct:153 | Mathlib（付値の整拡大への延長、`RingEquiv.piFinSucc`） | Mathlib の名前確認 | 段 1 ①③ |
| A6/Excision `sections_localEquiv_iso`・`sectionsOf_pushout` | S8-5・S8-4 | 1.12 | D5／段 G |
| A7/AnimatedDomain:69、A7/UniversalProperty:142・152、A7/AnimatedPerfectoidization:111・129 | A2 の sifted 延長・HT 単位・基底移送・Frobenius | A2 `exists_siftedExtension`・`animatedCAlgRealization`・`hodgeTateUnitFromInput`・`deltaOverQuotientIso`・`derivedPrismaticFrobenius`（BS-D4） | 中身の段階で置換 |
| A8 | 基盤の未確定名は 0 件（BS-D2） | — | — |

## 3. 既存で足りる名前（依頼不要、確認済み）

`QCatAdjunction`（F1B/Adjunction。A2 の反射と同じ型）、`IsSiftedInfinity`・`exists_siftedExtension`・`SigmaPresheafInfinity`（F2）、`IsPresentable`（F2/Presentable）、
`IsInvertibleEdge`（Core/InvertibleEdgeLifting）、`FunctorIso`・`FunctorHom`・`VertexIso`（Core）、`JoinCone`・`JoinCocone`・`IsLimitCone`・`IsColimitCone`・`mapJoinCocone`（Core/Limit）、
`fullSubcomplexOnVertices`（Core/TerminalVertices）、`SpaceInfinity`・`spaceInfinity_quasicategory`・`SpaceInfinityFunctor`（F1/Categories/CatInfinity。D5-07）、`derivedInfinityBaseChange`・`discreteEmbedding`（**代数**の埋め込み。加群は `moduleSemifreeResolutionFunctor` ＋ `closedNerveInclusion`、D5-02）・`H`（Derived）、`suspensionFunctor`・`loopFunctor`（Stable）、
`derivedSuspensionShiftObjectIso`（Derived、Σ = [1]）、`cAlgForgetDerived`・`algebraEmbedding`・`CAlg_R`（EInfinity）、`koszulComplexOn`・`dgNerve.vertexEquiv`（HA／DGNerve）、Mathlib の `GrothendieckTopology`・`Sieve`・`Coverage`・`presheafToSheaf`・`pushout`。

## 4. ∞ レーンへの依頼（案。W2b の取り込み後に調整役が IF の指示書に起こす。**調整役の回答 11-03**（coordination.md 8ef332d45）を各行の備考に記した）

| # | 項目 | 使う側（drafts） | 備考 |
| --- | --- | --- | --- |
| 1 | **G3** `IsPresentable (derivedInfinityCategory A)` | S2 `derivedGlobalSections` の `hE`、A0 CechAlexander・PrismaticSite、A2、A5、A6 ArcSheafProperty | M12c、`Derived/`。StablePresentable の一般論から |
| 2 | **G12** `IsPresentable (CAlg_R A)`（HA 3.2.3.5。忘却の極限保存は既存） | `sheafification_exists_cAlg`、A2:122、A5 `perfectCoefficientPresentable` | EInfinity 側。回答：∞ の依頼に入れる |
| 3 | **G4** `IsPresentable E → IsPresentable (ihom (presheafShape 𝒞) E)`（HTT 5.5.3.6） | S4 | M12b。**既存で済む**（IF-G1 §4、11-04）：`F2.Presentable.functor_isPresentable (nerve 𝒞ᵒᵖ) hE` |
| 4 | **G6** presentable ＋ 小さい W ⇒ 局所置換の存在（HTT 5.5.4.15 前半） | S4 | M12b。**既存で済む**（IF-G1 §4）：`F2.Presentable.Localization.exists_bousfieldLocalEquivalenceReplacement hE w x`、反射まで `bousfield_isReflectiveSubcategory hE w`。S4 は BS-D6 で二段に分けて使う |
| 5 | **G8** 空間とのテンソル X ⊗ M と Map(X ⊗ M, F) ≃ Map(M, lim_{el X} F)（HTT 5.1.5・4.2.4） | S3 の証明、S4、S8-4 の一般部分 | M12b |
| 6 | **G9・G10** 効果的エピの Čech 脈体の実現（または Bousfield–Kan との比較）、Δ 上の極限 ＝ 全複体 | S3 `isLimitCone_iff_restrict_cech` の証明 | M12d、`HomotopyLimits/`。S3 の主張は型つきで、証明経路の選択はここ |
| 7 | **G13** `IsPresentable SpaceInfinity`（𝒮 自体は F1 の `SpaceInfinity` として既にある、D5-07）と、`Type u` → 𝒮 の離散埋め込み（離散前層 `discretePresheaf` の実体） | S8-1 `sheafification_exists_spaces`、`sectionsOf` の `HasLimit`、`sheafify_discrete_eq`、A6 Cor 8.12 | 回答：∞ レーン。IF-G1 §4（11-04）で承認：`discreteSpaceInclusion : nerve (Type u) ⟶ SpaceInfinity.{u}`（`IsFullyFaithful` つき）と `Is0TruncatedSpace` を F1 に供給予定。drafts の `Is0Truncated` との接続（点ごと、`discretePresheafInclusion` の頂点・辺の式）は BS-D6 |
| 8 | **導来テンソル ⊗^L の ∞ 関手**（少なくとも固定対象とのテンソル `tensorWith M : D(A) ⟶ D(A)` と対称性。HA には複体レベルの `derivedTensor*` の同型だけ） | Descendable の thick ⊗-ideal（`IsThickTensorIdeal.tensor`、(f)(h)）。A0 `hodgeTateCohomology`・`completion_tensor_koszul`・`derived_nakayama`・A2 (5) は f^* f_*・Koszul・CAlg の余積で回避できる | 回答：∞ レーン（β5 の一部、`Derived/Tensor/`）。IF-G1 §4（11-04）で承認：`tensorWith M : D A ⟶ D A`・`tensorLeft M`・対称性 `FunctorIso`。BS-D6 で `IsThickTensorIdeal.tensor := ∀ x M, P x → P ((tensorWith M).app _ x)` に替え、`IsDescendable` の本体と離散底の完備版も型にする。**M13 には含めない** |
| 9 | **S4・S5 の担当**（層化の存在と完全性。G4・G6・G8 の後） | `Sheafification J E` を仮定している全部（A0・A2・A5・A6） | 回答：**BS 側**が書く（G4・G6・G8・G7 を ∞ が供給）。BS の M12a に S4・S5 を加える |
| 10 | Core の小補題：`uliftFunctor.obj (nerve (SmallModel C)) ⟶ nerve C` の比較 | A0 `structurePresheafDerived` | 回答：∞ の依頼に入れる（存在確認のうえ、なければ Core に一つ） |

## 4.1 S3 の経路と IF-G2 の G9・G10（2026-11-04 決定、BS）

**経路 (c)：Quillen A による余終性**（候補 (a) 効果的エピの実現・(b) Bousfield–Kan は採らない）。
`cechShape d = uliftFunctor.map (nerveMap d.obj.rightOp)` が left cofinal なら、S3 の二つの同値は既存の
`isLimitCone_iff_restrict_of_leftCofinal`・`hasLimit_iff_restrict_of_leftCofinal`（Derived/CofinalLimitTransfer）から出る。
left cofinal は Quillen A で「各 V ∈ 𝒟 について nerve (CostructuredArrow d.obj.rightOp (op V)) が弱可縮」に帰着する。
この comma は ([n], s ∈ Hom(V, U)^{n+1}) の圏（積の錐で Hom(V, U_n) ≅ Hom(V, U)^{n+1}）で、弱終性から s₀ ∈ Hom(V, U) を取り、
T([n], s) := ([n+1], (s, s₀)) と自然変換 id → T・const([0], s₀) → T で縮約できる。**BS が書く**：comma の同一視と縮約（1 圏）。

**∞ に依頼する型（IF-G2 の G9 の差し替え）**：

```lean
-- (G9-1) left 側の nerve の Quillen A（既存の right 版 `F2.Presentable.nerveMap_isRightCofinal_of_weaklyContractible_comma` の双対）
lemma nerveMap_isLeftCofinal_of_weaklyContractible_comma
    {P Q : Type u} [Category.{u} P] [Category.{u} Q] (F : P ⥤ Q)
    (h : ∀ q : Q, IsWeaklyContractible (nerve (CostructuredArrow F q))) :
    IsLeftCofinal (nerveMap F)
-- (G9-2) 宇宙の持ち上げで left cofinal は保たれる（cechShape は uliftFunctor.map）
lemma IsLeftCofinal.uliftFunctor_map {A B : SSet.{u}} {f : A ⟶ B} (hf : IsLeftCofinal f) :
    IsLeftCofinal ((SSet.uliftFunctor.{u + 1, u}).map f)
-- (G9-3) 縮約の向きを逆にした版（既存 `nerve_isWeaklyContractible_of_contractionSpan` は T ⟶ 𝟭・T ⟶ const）
lemma nerve_isWeaklyContractible_of_contractionCospan
    {C : Type u} [Category.{u} C] (v : C) (T : C ⥤ C)
    (h0 : 𝟭 C ⟶ T) (h1 : (Functor.const C).obj v ⟶ T) :
    IsWeaklyContractible (nerve C)
```

Δ は `Type` なので、(G9-1) に `SimplexCategory` を直接入れるときの宇宙（`ULiftHom`/`AsSmall` など）の扱いは ∞ 側の判断でよい。drafts の `cechShape` の形に合えばよい。

**G10 は S3 には不要、応用で要る**：A0 CechAlexander（Čech–Alexander の Tot ＝ D(A) の Δ 上の極限、Rem 4.19）、Shared/CosimplicialEInfinity
`totEInfinity_isLimitCone`（忘却後の Δ 極限錐）、それを使う A1 の HT 比較の模型、A6 Prop 8.10（Čech 複体の完全性 ⇒ D(A) 値の層条件）。依頼する型：

```lean
-- (G10) 余単体的 A 加群の D(A) での Δ 上の極限は交代余面複体で計算される
theorem cosimplicialModule_limitCone (X : CosimplicialObject (ModuleCat.{u} A)) :
    ∃ c : JoinCone ((SSet.uliftFunctor.{u + 1, 0}).map (nerveMap X) ≫ discreteModuleEmbedding A),
      IsLimitCone c ∧
      ∀ i : ℤ, Nonempty (derivedInfinityHomology A i c.vertex ≃ₗ[A]
        ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).obj X).homology' i)
```

（`discreteModuleEmbedding` は drafts/DerivedGeneral/Truncation の BS 版。∞ 側に複体を D(A) に入れる関手があれば、頂点をその像で述べ、
ホモロジーの同型は系にしてよい。添字の `homology'` は非負次数の複体を ℤ 添字で読む仮の書き方。各次数の同型は、錐の脚と標準射が
両立する形にしてほしい。A6 で各次数の消滅、A0 で比較射を使う。）

## 5. 段 2 の点検表（中身を書く順）

1. ∞：G3・G4・G6・G7・G8・G12・G13（`IsPresentable SpaceInfinity` と離散埋め込み。𝒮 自体は既存）・⊗^L（β5）・Core の小補題 → BS：S4・S5。
2. BS M13：`completionReflection`・`cAlgCompletionReflection`・`completion_*`、Truncation、ScalarRestriction（D 版）。CAlg 版の置き場所は調整役。
3. BS Shared：Tot_{E∞}（関手形）、Bockstein の Leibniz、`completedForms_eq_derivedCompletion_of_boundedTorsion`。
4. A2（P_Σ・Δ・HT filtration・底変換）→ A1（HT 比較・結晶入力・Thm 6.4 の多項式）→ A3。
5. M14（P⁰）・M15（descendable、⊗^L の後）→ A4〜A7 → A5 の Prop 8.5。
6. S8（𝒮 の後）→ A6 の excision → A8 → A9。

## 6. 履歴

- 2026-11-03：作成（BS-D4 完了後。A0〜A9 に `True` なし、基盤側 53 件）。
- 2026-11-03（調整役回答、coordination.md 8ef332d45）：§4 の三つの穴に回答。𝒮・G13 は ∞（`SpaceInfinity`）、⊗^L は ∞（β5、M13 に含めない）、S4・S5 は BS。G12・Core の小補題も ∞ の依頼へ。依頼書は W2b 後に調整役が起こす。
- 2026-11-04（IF-G1 第一区切り、main 7bda72c3c）：drafts の仮名を本名に。`setsToKan`（drafts 版を削除）・`discreteSpaceInclusion`・`Is0TruncatedSpace` は F1/Categories/DiscreteSpace、`discretePresheaf_vertex` は `discreteSpaceInclusion_diagramVertex`、`discretePresheafInclusion` の辺は `discreteSpaceInclusion_presheafInclusion_edge` で閉じた。`tensorWith` は Derived/Tensor/Fixed、G8 は F2/Tensor/SetSections の `tensorSpaceFunctor_setWeightHom`（S4 の生成辺は IF-G2 の自然性待ち）、G3 は `derivedInfinityCategory_isPresentable`、Core は `smallModelNerveComparison`（A0 `structurePresheafDerived` の入口）。
- 2026-11-04（調整役了解）：G13・⊗^L の要望は IF-G1 §5 へ（計算式は `rfl`、本質像の定義、合成可能な自己関手）。
- 2026-11-04（BS-D6 完了、2074a8d9e）：Descendable の `tensor` 欄と `IsDescendable` の本体、離散底の完備版、S4 の二段化（G4・G6 の既存名で反射まで証明の形）、S8 の点ごとの接続。残る `True` は 4（§1.5 の 1、§1.7 の 3）。∞ への要望：`discreteSpaceInclusion` の頂点・辺の計算式（厳密な等号）、`Is0TruncatedSpace` ＝ 離散埋め込みの本質像。
- 2026-11-04（IF-G1 停止点 1、main 7401c3588）：G4・G6 は既存の F2 名で済む。⊗^L（`tensorWith`）と G13（`discreteSpaceInclusion`・`Is0TruncatedSpace`）は供給予定。BS 側の追従は BS-D6（`bhatt-scholze-codex-d6.md`）：Descendable の `tensor` 欄・`IsDescendable` の本体・完備版、S4 の二段化、S8 の点ごとの接続。
- 2026-11-03（調整役、main 90def3697）：BS-D5 の完了と依頼 7 の縮小を計画 M12 の行と coordination.md に反映。残る依頼 7 は `Type u` → 𝒮 の離散埋め込みと 0 切り捨ての公開名の照合の二つ。∞ への依頼書は W2b の取り込み後。
- 2026-11-03（BS-D5 終了）：53 件中 48 件を型に（残り 5 は Shared の × 理由つき）。`space_isPresentable` も F2 に既存で、∞ への依頼 7 は離散埋め込みの照合だけ。
- 2026-11-03（D5-07、Codex）：𝒮 は F1 に `SpaceInfinity` として既にあった（入口表の「名前がない」は誤り）。S8 は実体を参照し、要確認は `IsPresentable` と離散前層の接続だけ。∞ への依頼 7 はその二つに縮む。
- 2026-11-03（D5-06、Codex）：S1-E は `FinitaryExtensive`（非交叉性つき）で述べる。`FinitaryPreExtensive` だけでは偽（0 < 1 の被覆 {1→1, 1→1}）。A6 の site では非交叉性を別に示す。
- 2026-11-03（D5-05、Codex）：Shared/CosimplicialCupProduct の既存の入口 `cohomologyEquivHomology` が未定義名 `CosimplicialObject.alternatingCofaceMapComplex` を使っていた。Mathlib の実名は `AlgebraicTopology.alternatingCofaceMapComplex C`、忘却は CommRingCat → RingCat → AddCommGrpCat の合成。名前・引数・主張を保って直す（Bockstein の `CosimplicialShortExact.bockstein` も同じ）。
- 2026-11-03（D5-04、Codex）：`isDescendable_of_faithfullyFlat` は忠実平坦＋有限表示に限定（Mathew Prop 3.31。忠実平坦だけでは偽、Aoki arXiv:2411.05995）。
- 2026-11-03（D5-03、Codex）：P⁰ は φ_k 半線形。`powerOperationZero_natTrans` は U ⇒ U ≫ `derivedInfinityRestrictScalars (frobenius k p)` の形にし、k = F_p で自己変換に特殊化。
- 2026-11-03（D5-02、Codex）：`discreteEmbedding A` は A 代数用。加群 H^n(X)・Ω^i は `moduleSemifreeResolutionFunctor` ＋ `closedNerveInclusion`（A2 `ordinaryFormsDiagram` と同じ）で入れる。§1.2・§1.6 を訂正、`discreteModuleEmbedding` を新設。
- 2026-11-03（D5-01、Codex）：§1.2 の shift の式を `IsConnectiveAt n x ↔ IsConnectiveAt (n-1) (Σx)` に訂正、分解は τ^{≤n} → id → τ^{≥n+1} の cofiber＝fiber 四角形。
