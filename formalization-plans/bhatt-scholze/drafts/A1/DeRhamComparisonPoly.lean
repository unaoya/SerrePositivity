-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.DeRhamComparisonPoly（仮。原典 Thm 6.4 の多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §9、単位 A1-5。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
-- 本ファイルは drafts/A1/{CrystallineInput,HodgeTateComparison,HodgeTateMap}.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A2/BaseChangeAndTensor.lean、
-- drafts/A3/LciAndQuasiregular.lean（D4-02 の特殊化だけ）、drafts/A5/RootAdjunction.lean（`polyRootAlgebra`。W9-III-09：WeaklyInitialAndDescent ではなく先行ファイル）を import する。
-- J つき pd 模型（`pdModel`・`pdPolynomialComparison`）と `formsCAlg` は drafts/A1/CrystallineInput.lean（W9-III-09）。D68 改訂（11-05 夜）で結晶の黒箱は外した。

/-!
# de Rham 比較の多項式・mod p の場合（BS 著者版 Thm 6.4 の特別な場合、A1-5）

## 概要
完全 prism (A,(d))、R = A/d、T = R⟨X_1,…,X_n⟩ について φ_A^*Δ_{T/A} ⊗̂^L_A A/(p,d) ≃ Ω^*_{(T/p)/(R/p)}（D(R/p) の可換代数の自然な同型）。
T_∞ = R⟨X_i^{1/p^∞}⟩ では ≃ T_∞/p。Lemma 8.6（A5-3）の入力。

## 方針
D69（a1-design §9.1、W9-I-15 の訂正後）：完全 prism ← 普遍向き付き prism A_0（Cor 4.12 の底変換）、A_0 上では原典 Thm 6.4 の証明
（ψ : A_0 → W(A_0/d_0)、Thm 5.2 β の J つき模型 `wittPdBridge`、J つき pd 比較 G-A1-17、w_0 に沿う底変換）。D68 改訂（11-05 夜）で
結晶の黒箱はなくなった：Thm 5.2 β は Lemma 5.4（A1/CrystallineInput）と導来 Nakayama で `wittPdBridge` の中で示す。可換代数構造は各段で保つ。

## 規約
Frobenius 捻り φ^*Δ ⊗ A/(p,d) = Δ ⊗_A A/(p, φ^{-1}(d))（完全 prism）。de Rham 複体は Shared/DeRhamPolynomial の cdga を CAlg に。

## 使われ方
A5-3 `rootMap_modP_eq_deRham`。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.BhattScholze.Perfectoidization.Derived
open SerrePositivity.DerivedCompletion
variable (p : ℕ) [Fact p.Prime]

/-- p 完備 CAlg への反射。底の D(k) で完備性を判定する。 -/
def primeCompleteAlg (k : Type u) [CommRing k] :=
  fullSubcomplexOnVertices (CAlg_R k) (fun X => completeAt (p : k) ((cAlgForgetDerived k).app _ X))
instance (k : Type u) [CommRing k] : Quasicategory (primeCompleteAlg p k : SSet) :=
  fullSubcomplexOnVertices_quasicategory _ _
def primeAlgReflection (k : Type u) [CommRing k] :
    Σ L : CAlg_R k ⟶ (primeCompleteAlg p k : SSet), QCatAdjunction L (primeCompleteAlg p k).ι := by
  sorry -- 要確認：G-A2-9 の主元 p に対する CAlg 完備反射
abbrev primeAlgCompletion (k : Type u) [CommRing k] := (primeAlgReflection p k).1 ≫ (primeCompleteAlg p k).ι
abbrev completeChange {k l : Type u} [CommRing k] [CommRing l] (g : k →+* l) :=
  cAlgBaseChange g ≫ primeAlgCompletion p l

abbrev U := universalOrientedPrism.{u} p
abbrev residueU := universalOrientedPrismRing.{u} p ⧸ (U p).ideal
abbrev qU := Ideal.Quotient.mk (U.{u} p).ideal
abbrev WU := WittVector p (residueU.{u} p)

def psiRing : universalOrientedPrismRing.{u} p →+* WU p :=
  WittVector.frobenius.comp ((WittVector.map (qU p)).comp
    (deltaWittGhostRingHom (U p).deltaStructure (by sorry))) -- A₀ は p 正則なので ghostMap は単射

def wittCrystallinePrism : OrientedPrism p (WU.{u} p) := by
  let hp : Function.Injective (fun x : WU.{u} p => (p : WU p)*x) := by sorry -- C=A₀/d₀ は p 正則
  let D := (DeltaStructure.existsUnique_of_mod_p hp WittVector.frobenius
    (by sorry)).exists.choose -- Witt Frobenius は mod p で p 乗
  letI : IsAdicComplete (Ideal.span {(p : WU.{u} p)}) _ := by sorry -- C の p 完備性から Witt 座標で取る
  exact OrientedPrism.crystalline D hp

def psiPrism : OrientedPrism.Hom (U.{u} p) (wittCrystallinePrism p) where
  toRingHom := psiRing p
  map_delta := by sorry -- Witt の標準射と F は Frobenius と可換、標的は p 正則
  ideal_le := by sorry -- can(d₀) の第 0 成分は零、V の像に F を作用させると p の倍数
abbrev wZero : WU.{u} p →+* residueU p := WittVector.constantCoeff
theorem wZero_psi : (wZero.{u} p).comp (psiRing p) = (qU p).comp (U p).deltaStructure.frobeniusLift := by
  sorry -- deltaWittGhostRingHom_frobenius_comp と constantCoeff の合成則

abbrev wittPdIdeal := RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : residueU.{u} p)})).comp (wZero p))
def wittPdStructure : DividedPowers (wittPdIdeal.{u} p) := by
  sorry -- Thm 6.4 の J。V(W(C)) と p の標準 divided powers は共通部分で一致

abbrev universalTwist :=
  polyUnderlying (U.{u} p) (universalOrientedPrism_bounded (p := p)) ≫
    completeChange p ((qU p).comp (U p).deltaStructure.frobeniusLift)

abbrev wittPrismBounded := crystallineBounded p (wittCrystallinePrism.{u} p) rfl
abbrev wittPolynomial (n : ℕ) := polynomialDelta (wittCrystallinePrism.{u} p) (wittPrismBounded p) n

def psiBaseChange (n : ℕ) : VertexIso
    ((polyUnderlying (U p) (universalOrientedPrism_bounded (p := p)) ≫
      completeChange p (psiRing p)).app _ (polyPoint (residueU.{u} p) n)) (wittPolynomial p n) := by
  have hc := prismaticCohomology_baseChange' (U p) (universalOrientedPrism_bounded (p := p)) n
    (wittCrystallinePrism p) (wittPrismBounded p) (psiPrism p)
  sorry -- hc による標準同型。W の (p,p) 完備化を p 完備化と同定し polyDeltaData.obj_eq で移送

def wittPdBridge (n : ℕ) : VertexIso (wittPolynomial.{u} p n)
    (Cosimplicial.totEInfinity (WU p) (pdModel p (WU p) n)) := by
  sorry -- ψ̄ による多項式入力と Thm 5.2 β の相対 Frobenius の模型を同定し、
        -- J つき pd 脈体に移す。splitDeltaCoordinates の追加座標と extraCech_comparison を係数拡大。
        -- 11-07：W 上の Thm 5.2 β は整係数で要る（C = A₀/d₀ は p ねじれなし）。mod p は Lemma 5.4
        -- （frobeniusTwist_cech_quasiIso_infinite、k = W/p）、持ち上げは導来 Nakayama（G-A1-4）

/-- 三つの矢印の合成で D69 の比較射を固定する。最後の係数射は w₀。 -/
structure WittComparisonLegs (n : ℕ) where
  regroup : VertexIso ((universalTwist.{u} p).app _ (polyPoint _ n))
    ((polyUnderlying (U p) (universalOrientedPrism_bounded (p := p)) ≫ completeChange p (psiRing p) ≫
      completeChange p (wZero p)).app _ (polyPoint _ n))
  crystalline : VertexIso ((polyUnderlying (U p) (universalOrientedPrism_bounded (p := p)) ≫
    completeChange p (psiRing p)).app _ (polyPoint _ n))
    (Cosimplicial.totEInfinity (WU p) (pdModel p (WU p) n))
  pd : VertexIso (Cosimplicial.totEInfinity (WU p) (pdModel p (WU p) n)) (formsVertex p (WU p) n)
  liftChange : VertexIso ((completeChange p (wZero p)).app _ (formsVertex p (WU p) n)) (formsVertex p (residueU p) n)

def wittComparisonLegs (n : ℕ) : WittComparisonLegs.{u} p n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · sorry -- wZero_psi と完備係数拡大の推移律
  · exact psiBaseChange p n ≪≫ wittPdBridge p n
  · exact (pdPolynomialComparison p _ (wittPdIdeal p) (wittPdStructure p)
      (by sorry) (by sorry) (by sorry) (by sorry)).app n -- p∈J、標準 pd と両立、W は p 完備・p 正則
  · sorry -- 多項式持ち上げの連続 de Rham 複体を w₀ に沿って完備底変換

def wittComposite (n : ℕ) :=
  let L := wittComparisonLegs.{u} p n
  L.regroup ≪≫ (L.crystalline.map (completeChange p (wZero p))) ≪≫
    (L.pd.map (completeChange p (wZero p))) ≪≫ L.liftChange

/-- 概要：A_0 上の比較同型（原典 Thm 6.4 の証明を A_0 で、D69）。成分は `wittComposite`。
方針：成分ごとの同型を関手 ∞ 圏の同型に貼る。
規約：**TODO（11-07、a1-design §10.4）**：貼り合わせの高次の整合性が未設計。`FunctorIso` は Fun(N(Poly), CAlg) のホモトピー圏の同型で、
成分の同型とホモトピー圏での自然性（G-A1-17 の `natural`・`changeLift`、1 単体まで）からは作れない（自然変換は N(Poly) × Δ¹ → CAlg の写像）。
要る ∞ 側の部品：(i) 両辺を選択なしで厳密に関手的な模型（Poly(C) 上の大きい J つき pd Čech 模型、持ち上げの選択を使わない）の
厳密な自然変換の zigzag として与えること、(ii) `Cosimplicial.totEInfinityFunctor` と、厳密な自然変換の脈体 N(𝒞 × [1]) ≅ N𝒞 × Δ¹ から
関手単体集合の辺を作る部品、(iii) 成分ごとに可逆な辺は可逆（本体 `functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise`）。
代案（要相談）：使う側（`deRham_iso_rootAlgebra_modP` → A5 `rootMap_modP_eq_deRham`）は成分ごとの同型と根の遷移 X ↦ X^p の可換な四角形しか使わないので、
型を「各 n の `VertexIso` ＋ X ↦ X^p についての自然性」に弱めれば貼り合わせは要らない（N(ℕ) の背骨は内側 anodyne）。
使われ方：`transferWittComparison`。 -/
def deRham_iso_polynomial_universal :
    { e : FunctorIso (universalTwist.{u} p) (formsCAlg p (residueU p)) //
      ∀ n, e.app (polyPoint _ n) = wittComposite p n } := by
  sorry -- TODO（a1-design §10.4）：高次の整合性。G-A1-17 の 1 単体までの自然性だけでは貼れない。
        -- 保存性から同型を選ぶ手順は使わない

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
abbrev modOrientation : A →+* modPrime p (A ⧸ P.ideal) :=
  (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (Ideal.Quotient.mk P.ideal)
abbrev twistedReduction := (modOrientation p P).comp P.deltaStructure.frobeniusLift
abbrev reducedPolyDelta := polyUnderlying P hP ≫ completeChange p (twistedReduction p P)
abbrev reducedPolyForms := changePolyNerve (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})) ≫
  formsCAlg p (modPrime p (A ⧸ P.ideal))

/-- A₀ で既に構成した射を d₀↦d に沿って移す。 -/
abbrev residueToModP := (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ P.ideal)})).comp (orientationMap P).quotientMap

def universalDeltaChange (n : ℕ) : VertexIso ((reducedPolyDelta p P hP).app _ (polyPoint _ n))
    ((completeChange p (residueToModP p P)).app _ ((universalTwist p).app _ (polyPoint _ n))) := by
  sorry -- 分類射による polynomialChangeEdge は Cor 4.12 で可逆。
        -- δ 射と φ の両立、完備底変換の結合則でその逆を取る
def universalFormsChange (n : ℕ) : VertexIso
    ((completeChange p (residueToModP p P)).app _ (formsVertex p (residueU p) n))
    ((reducedPolyForms p P).app _ (polyPoint _ n)) := by
  sorry -- 有限自由な連続形式の底変換。座標とその微分を同じ座標へ送る

def transferWittComparison (hperf : P.deltaStructure.IsPerfect) :
    { e : FunctorIso (reducedPolyDelta p P hP) (reducedPolyForms p P) // ∀ n : ℕ,
      e.app (polyPoint _ n) = universalDeltaChange p P hP n ≪≫
        ((deRham_iso_polynomial_universal p).val.app (polyPoint _ n)).map (completeChange p (residueToModP p P)) ≪≫
        universalFormsChange p P n } := by
  sorry -- 普遍例で構成した比較を分類射に沿って移す。係数・多項式の持ち上げに関する
        -- J つき比較の自然性により各成分が多項式射と可換

def deRham_iso_polynomial_modP (hperf : P.deltaStructure.IsPerfect) :
    FunctorIso (reducedPolyDelta p P hP) (reducedPolyForms p P) :=
  (transferWittComparison p P hP hperf).val

abbrev rootSource (C : Type u) [CommRing C] := formsVertex p C 1
abbrev rootTargetAlgebra (n : ℕ) : A_R (modPrime p (A ⧸ P.ideal)) := by
  let R := A ⧸ P.ideal
  let S := polyRootAlgebra p R n
  exact Under.mk (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(p : S)}) (algebraMap R S) (by
    sorry))) -- p の像は p

abbrev rootStrictTarget (n : ℕ) :=
  (commAlgCatEquivUnder (CommRingCat.of (modPrime p (A ⧸ P.ideal)))).inverse.obj (rootTargetAlgebra p P n)

def rootDegreeZeroMap (n : ℕ) :
    MvPolynomial (Fin n) (modPrime p (A ⧸ P.ideal)) →ₐ[modPrime p (A ⧸ P.ideal)] (rootStrictTarget p P n) :=
  let C := modPrime p (A ⧸ P.ideal)
  MvPolynomial.aeval (R := C) (fun j : Fin n =>
    Ideal.Quotient.mk (Ideal.span {(p : polyRootAlgebra p (A ⧸ P.ideal) n)})
      (polyRootAlgebraVar p (A ⧸ P.ideal) n j 0))

abbrev singleRootTarget (n : ℕ) :=
  let C := modPrime p (A ⧸ P.ideal)
  (CochainComplex.singleFunctor (ModuleCat C) 0).mapCommMon.obj
    ((moduleCommMonoidFunctor C).obj (rootStrictTarget p P n))

def polynomialZeroForm (C : Type u) [CommRing C] (n : ℕ) :
    MvPolynomial (Fin n) C →+ (formComplex p C n).X 0 := by
  sorry -- Ω⁰=多項式環を ULift の変数に rename、completedFormsUnit と extendXIso で次数零へ
def singleTargetZeroIso (n : ℕ) :
    (singleRootTarget p P n).X.X 0 ≃+ (rootStrictTarget p P n) := by
  sorry -- HomologicalComplex.singleObjXSelf の底の加法同型

def cdgaAugmentation (n : ℕ) :
    let C := modPrime p (A ⧸ P.ideal)
    { f : formsCDGA p C n ⟶ singleRootTarget p P n //
      ∀ a : MvPolynomial (Fin n) C, singleTargetZeroIso p P n
        (f.hom.hom.f 0 (polynomialZeroForm p C n a)) = rootDegreeZeroMap p P n a } := by
  sorry -- 次数零は rootDegreeZeroMap（p=0）、正次数では標的が零。
        -- 単位・外積・微分に両立する CommMon の射を作る

def rootFormsAugmentation (n : ℕ) :
    SSet.Edge (formsVertex p (modPrime p (A ⧸ P.ideal)) n)
      ((algebraEmbedding _).app _ (nerveVertex (rootTargetAlgebra p P n))) := by
  let C := modPrime p (A ⧸ P.ideal)
  let F := commutativeAlgebraFunctor C ⋙ Operad.restrictAlgebra (augmentation C)
  let e := (nerve.edgeMk (F.map (cdgaAugmentation p P n).val)).map (algebraCAlgSource C)
  exact e -- 同じ cofibrant 置換により両端は formsVertex と離散代数の像

def rootArrow (n : ℕ) : ofAlgebra (A ⧸ P.ideal) (polyAlgebra p (A ⧸ P.ideal) n) ⟶
    ofAlgebra (A ⧸ P.ideal) (polyRootAlgebra p (A ⧸ P.ideal) n) :=
  Under.homMk (CommRingCat.ofHom (polyAlgebraToRoot p _ n)) (by sorry) -- 両端の係数を保つ
abbrev rootDeltaEdge (n : ℕ) := (nerve.edgeMk (rootArrow p P n)).map
  (derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫ completeChange p (twistedReduction p P))

/-- 完備離散入力 T での値を polyUnderlying の多項式頂点に移送する。 -/
def completedPolynomialRecovery (n : ℕ) :
    VertexIso ((derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫
      completeChange p (twistedReduction p P)).app _ (nerveVertex (ofAlgebra _ (polyAlgebra p (A ⧸ P.ideal) n))))
      ((reducedPolyDelta p P hP).app _ (polyPoint _ n)) := by
  sorry -- A2 の polyRecovery、離散多項式の p 完備化は有界ねじれで次数零、D32

theorem deRham_iso_rootAlgebra_modP (hperf : P.deltaStructure.IsPerfect) (n : ℕ) :
    let g := rootFormsAugmentation p P n
    let e := completedPolynomialRecovery p P hP n ≪≫ (deRham_iso_polynomial_modP p P hP hperf).app (polyPoint _ n)
    ∃ e∞ : VertexIso ((derivedPrismaticCohomologyDiscrete P hP ≫ prismCompleteInclusion P ≫
        completeChange p (twistedReduction p P)).app _ (nerveVertex (ofAlgebra _ (polyRootAlgebra p (A ⧸ P.ideal) n))))
        ((algebraEmbedding _).app _ (nerveVertex (rootTargetAlgebra p P n))),
      HomotopyCategory.homMk (rootDeltaEdge p P hP n) ≫ e∞.hom = e.hom ≫ HomotopyCategory.homMk g := by
  sorry -- X_j↦X_j^p の列の完備 filtered 余極限。mod p で正次数の形式の遷移は零、
        -- 次数零は T∞/p。最初の余極限脚で可換式を得る

/-! A3 は A2 の底変換を使うため、普遍例への特殊化は A1 の最終ファイルに置く。 -/
theorem prismaticCohomology_lci_universal {r : ℕ} (f : Fin r → A)
    (hf : IsKoszulRegularModGenerator P f) (hb : BoundedPTorsion p (lciQuotient P f)) :
    let R := lciQuotient P f
    let h := lci_isDiscretePrismatic P hP f hf hb
    ∃ t : InitialDelta P hP R h, IsLciEnvelope P f (discretePrism P hP R h t.D t.base) (discreteBase P hP R) := by
  obtain ⟨g, hg, _⟩ := universalOrientedPrism_hom P
  exact prismaticCohomology_lci_eq_envelope P hP f (U p) (universalOrientedPrism_bounded (p := p)) g hg hf hb

end SerrePositivity.BhattScholze.Prismatic
