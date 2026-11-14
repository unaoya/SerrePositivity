-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.StrongDescent（仮。原典 Lemma 8.6）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §2.4・§3.5、単位 A5-3。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.Algebra.Homology.Double
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.HeartFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BaseChange
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.Koszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
-- 本ファイルは drafts/Shared/Descendable.lean、drafts/Shared/DeRhamPolynomial.lean、drafts/A5/{PerfectSite,RootAdjunction}.lean（W9-III-09：PerfectSiteComparison・WeaklyInitialAndDescent は本ファイルより後）、
-- drafts/A2/BaseChangeAndTensor.lean、drafts/DerivedGeneral/Truncation.lean、drafts/A1/（A1-5：Thm 6.4 の多項式・mod p）を import する。

/-!
# 完全化への移行の強い降下（BS 著者版 Lemma 8.6）

## 概要
T = R⟨X_1,…,X_n⟩ → T_∞ = R⟨X_i^{1/p^∞}⟩ について、Δ_{T/A} → Δ_{T_∞/A} と Δ_{T/A,perf} → Δ_{T_∞/A,perf} は D_comp(A) の可換代数の射として
descendable。

## 方針
perf 版は非 perf 版と [BS17, Lemma 11.22]（Descendable の (g)）。非 perf 版は n = 1 に帰着（(5) とテンソル (c)）。n = 1：F = fib(Δ_T → Δ_{T_∞})
について RHom_{Δ_T}(F^{⊗2}, Δ_T) ∈ D^{<0} を示す（(f)）。完備性で A → A/(p, φ^{-1}(d)) の底変換後に確かめればよく（G-A5-6）、
Δ_T ⊗_A A/φ^{-1}(d) = φ_A^*Δ_T ⊗_A A/d は de Rham 比較（A1-5：Thm 6.4 の多項式・mod p）で Ω^•_{(T/p)/(R/p)}、T_∞ では L = 0 で T_∞/p。
一変数の Cartier で Ω^• は分裂二乗零拡大 Ω = T ⊕ Ω^1[−1] と cdga として擬同型（G-A5-12）、(∗) の dg 加群の計算（G-A5-13）。

## 規約
descendable は Shared/Descendable（Mat16 の定義）。de Rham 入力は A1-5 の定理（黒箱にしない、決定 3）。

## 使われ方
A5-4 の降下（`prismaticPerfection_rootCover_descent`）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

open SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

def polynomialRootArrow (n : ℕ) : ofAlgebra R (polyAlgebra p R n) ⟶ ofAlgebra R (polyRootAlgebra p R n) :=
  Under.homMk (CommRingCat.ofHom (polyAlgebraToRoot p R n)) (by
    sorry) -- 完備化前の変数の包含は R 上、completionMap_comp で完備化後も R 上

abbrev deltaRootEdge (n : ℕ) :=
  (nerve.edgeMk (polynomialRootArrow p R n)).map (discreteDeltaFunctor (E := E) p R hR)

abbrev perfRootEdge (n : ℕ) :=
  (nerve.edgeMk (polynomialRootArrow p R n)).map (directPerfectionFunctor (E := E) p R hR)

/-- 概要：Lemma 8.6（非 perf 版）：Δ_{T/A} → Δ_{T_∞/A} は D_comp(A) で descendable。
方針：`rootMap_descendable_one` と n への帰着。
規約：`IsDescendableOver`（完備版 (h)）。
使われ方：perf 版。 -/
theorem prismaticCohomology_rootMap_descendable (n : ℕ) : IsDescendableOver (E := E) (perfectPrismRing p R) _ _ (deltaRootEdge (E := E) p R hR n) := by
  sorry -- 一変数の index 判定とテンソルによる帰着。Shared/Descendable の (c)(d)(h) 待ち

/-- 概要：Lemma 8.6（perf 版）：Δ_{T/A,perf} → Δ_{T_∞/A,perf} は descendable（(g)：非 perf 版の index の上界 m から perf 版は ≤ 2m。n は変数の個数で index ではない、
W9 §8.7。結論は `IsDescendableOver` でよく数値は公開しない）。A5-1 の主張の証明。
方針：非 perf 版と `hasDescentIndexLEOver_frobeniusColimit`、完備化。
規約：—
使われ方：A5-4。 -/
theorem prismaticPerfection_rootMap_descendable' (n : ℕ) : IsDescendableOver (E := E) (perfectPrismRing p R) _ _ (perfRootEdge (E := E) p R hR n) := by
  sorry -- Shared/Descendable の (g)(h) 待ち。半線形な塔の index 上界を余極限と完備化へ移す

/-! ## n = 1 への帰着 -/

/-- 概要：Δ_{T_n/A} = Δ_{T_1/A}^{⊗̂_A n}、Δ_{T_{n,∞}} も同様（(5)）。descendable のテンソル (c) で n = 1 に帰着。
方針：A2-4 `derivedPrismaticCohomology_tensor`。
規約：—
使われ方：上。 -/
theorem rootMap_descendable_of_one (h : IsDescendableOver (E := E) (perfectPrismRing p R) _ _ (deltaRootEdge (E := E) p R hR 1)) (n : ℕ) :
    IsDescendableOver (E := E) (perfectPrismRing p R) _ _ (deltaRootEdge (E := E) p R hR n) := by
  sorry -- n=0 は恒等射。(5) により両端を一変数の n 重完備テンソルと同定。
        -- Shared/Descendable の isDescendableOver_tensor と完備版 (h) 待ち

/-! ## n = 1 -/

abbrev inverseGenerator := Andre.perfectPrismVarpiLift (perfectPrism p R hR) (perfectPrism_isPerfect p R hR)
abbrev inversePair : Ideal (perfectPrismRing p R) := Ideal.span {(p : perfectPrismRing p R), inverseGenerator p R hR}
abbrev rootTestCoefficients := perfectPrismRing p R ⧸ inversePair p R hR

/-- M15 の Mod_D における内部 Hom の台。F=fib(f)、N=F⊗_D F として
RHom_D(N,D⊗_A L) を D(A) に忘れる。L を後からテンソルする交換則は含めない。 -/
def fiberSquareRHom {A : Type u} [CommRing A] {D B : (E.CAlg A) _⦋0⦌}
    (f : SSet.Edge D B) (L : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌ := by
  sorry -- 要確認：M15 の Mod_D の fiber・相対テンソル・内部 Hom の忘却

abbrev rootDual := fiberSquareRHom (E := E) (deltaRootEdge (E := E) p R hR 1)
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex (perfectPrismRing p R) (ModuleCat.of _ (perfectPrismRing p R)))

/-- 概要：F := fib(Δ_T → Δ_{T_∞}) ∈ D(Δ_T)。RHom_{Δ_T}(F^{⊗2}, Δ_T) ∈ D^{<0} なら index ≤ 2（(f)）。
方針：Shared/Descendable の `hasDescentIndexLEOver_two_of_rhom`。
規約：テンソルは D(Δ_T)。
使われ方：`rootMap_descendable_one`。 -/
theorem rootMap_fiber_rhom_coconnective :
    Derived.IsConnectiveAt (perfectPrismRing p R) (-1) (rootDual (E := E) p R hR) := by
  sorry -- G-A5-13 の任意係数版と rhom_baseChange_koszul_connection、D^{≤−1}

/-- 概要：G-A5-6：導来 (p,d) 完備な M で M ⊗^L_A A/(p, φ^{-1}(d)) ∈ D^{<0} ⇒ M ∈ D^{<0}（最高次の H は完備で Nakayama）。
(p, φ^{-1}(d)) と (p,d) は同じ根基。
方針：DerivedGeneral/Truncation の `derived_nakayama` の上界版。
規約：—
使われ方：底変換後に確かめる。 -/
theorem coconnective_of_modBaseChange (M : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory (perfectPrismRing p R)) _⦋0⦌)
    (hp : IsComplete (perfectPrismRing p R) (p : perfectPrismRing p R)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence _).functor.obj ⟨M⟩))
    (hd : IsComplete (perfectPrismRing p R) (perfectPrism p R hR).generator
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence _).functor.obj ⟨M⟩))
    (hC : Derived.IsConnectiveAt (rootTestCoefficients p R hR) (-1)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (Ideal.Quotient.mk (inversePair p R hR))).app _ M)) :
    Derived.IsConnectiveAt (perfectPrismRing p R) (-1) M := by
  sorry -- 商環上の離散加群にテンソルしても上界を保つ。Koszul の有限 filtration と完備性を使う

/-- CAlg の係数拡大は係数制限の左随伴。D3-05 の一般形は `cAlgBaseChange`、
忘却した底変換との比較は `cAlgBaseChange_forget`（DerivedGeneral/ScalarRestriction）。 -/
def prismScalarExtension {A C : Type u} [CommRing A] [CommRing C] (q : A →+* C) : E.CAlg A ⟶ E.CAlg C :=
  Classical.choose (show ∃ G, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction G (cAlgRestrictScalars (E := E) q)) from by
    sorry) -- cAlgBaseChange と cAlgBaseChange_restrictScalars_adjunction（D3-05、M13）

abbrev reducedRootEdge := (deltaRootEdge (E := E) p R hR 1).map
  (prismScalarExtension (E := E) (Ideal.Quotient.mk (inversePair p R hR)))

abbrev testKoszulComplex := SerrePositivity.DerivedCompletion.powerKoszulTower (perfectPrismRing p R)
  (SerrePositivity.DerivedCompletion.pairKoszulCoordinates (perfectPrismRing p R)
    (p : perfectPrismRing p R) (inverseGenerator p R hR)) 1

def koszulVertex :=
  (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence (perfectPrismRing p R)).inverse.obj
    (DerivedCategory.Q.obj (testKoszulComplex p R hR)))).pt

def rootDualTensorKoszul :=
  (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence (perfectPrismRing p R)).inverse.obj (DerivedCategory.Q.obj
    (cochainTensor ((rootDual (E := E) p R hR).obj 0).val (testKoszulComplex p R hR))))).pt

/-- 概要：G-A5-6′（W9-II-12。W9 続き 6 で紙 ○）：D := Δ_T、N := F ⊗^L_D F、M := RHom_D(N, D)、e := φ_A^{-1}(d)、C := A/(p,e)。M は導来 (p,e) 完備。
C が perfect であることも M ⊗^L_A C と底変換後の RHom の一致も仮定しない。
方針：(1) 任意の離散 C 加群 L について RHom_{D_C}(N_C, D_C ⊗^L_C L) ∈ D^{≤−1}（`squareZero_rhom_coconnective` の任意係数版）。(2) 随伴で
RHom_D(N, D ⊗^L_A L) ≃ RHom_{D_C}(N_C, D_C ⊗^L_C L) ∈ D^{≤−1}。(3) 有限 Koszul 複体 K := K_A(p,e)（双対可能、H^j(K) は j ∈ [−2,0] の C 加群）の有限 Postnikov
filtration の段階 H^j(K)[−j] に (2) を当て RHom_D(N, D ⊗^L_A K) ∈ D^{≤−1}；双対可能性でここで初めて RHom とテンソルを交換し M ⊗^L_A K。(4) K(p^n,e^n) は K から
有限拡大で、遷移の最高次コホモロジーが全射なので M ≃ Rlim_n(M ⊗^L_A K(p^n,e^n)) に lim¹ の次数 0 の項はなく M ∈ D^{≤−1}。原典 "By completeness" の一文の形式化。
規約：(p,e) と (p,d) は同じ根基。
使われ方：`rootMap_fiber_rhom_coconnective`。 -/
theorem rhom_baseChange_koszul_connection
    (h : ∀ L : ModuleCat.{u} (rootTestCoefficients p R hR),
      Derived.IsConnectiveAt (rootTestCoefficients p R hR) (-1)
        (fiberSquareRHom (E := E) (reducedRootEdge (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex _ L))) :
    let A := perfectPrismRing p R
    let MK := fiberSquareRHom (E := E) (deltaRootEdge (E := E) p R hR 1) (koszulVertex p R hR)
    Derived.IsConnectiveAt A (-1) MK ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso MK (rootDualTensorKoszul (E := E) p R hR)) ∧
      Derived.IsConnectiveAt A (-1) (rootDual (E := E) p R hR) := by
  sorry -- 随伴で全ての L の評価を A 上に戻す。pairKoszulTower の有限 Postnikov 各段に適用し、
        -- 双対可能な K でのみ Hom とテンソルを交換する。冪の塔の最高次は全射、Rlim の lim¹ は零

/-- 概要：A/(p, φ^{-1}(d)) ≅ R/p（φ_A が自己同型で A/φ^{-1}(d) ≅_φ A/d = R）。Δ_T ⊗_A A/φ^{-1}(d) = φ_A^*Δ_T ⊗_A A/d。
方針：完全 prism の φ_A。
規約：—
使われ方：de Rham 比較を当てる。 -/
theorem baseChange_phiInv_eq_frobeniusTwist :
    let A := perfectPrismRing p R
    let φ := (perfectPrism p R hR).deltaStructure.frobeniusLift
    let I := Ideal.span {inverseGenerator p R hR}
    ∃ e : rootTestCoefficients p R hR ≃+* R ⧸ Ideal.span {(p : R)},
      (∀ a : A, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (perfectPrismTheta p R hR (φ a))) ∧
      ∃ v : A ⧸ I ≃+* R, v.toRingHom.comp (Ideal.Quotient.mk I) = (perfectPrismTheta p R hR).comp φ ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (Ideal.Quotient.mk I) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange v.toRingHom)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange φ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange (perfectPrismTheta p R hR))) := by
  sorry -- φ は自己同型で (p,e) を (p,d) に送る。perfectPrism_quotientEquiv を mod p で合成

/-- 一変数の de Rham cdga の E∞ 実現と、その T_∞/p への射。次数零は X を
T_∞/p の標準変数に送り、dX を 0 に送る。両者を φ を通じた C=R/p の代数とみなす。 -/
def rootDeRhamSource (C : Type u) [CommRing C] : (E.CAlg C) _⦋0⦌ := by
  sorry -- 要確認：DeRham.deRhamComplex C (Fin 1) の外積付き cdga を E∞ 代数へ実現（A1-5）

def rootModPAlgebra : A_R (rootTestCoefficients p R hR) := by
  let B := polyRootAlgebra p R 1
  let T := B ⧸ Ideal.span {(p : B)}
  let e := (baseChange_phiInv_eq_frobeniusTwist p R hR).choose
  let g : R ⧸ Ideal.span {(p : R)} →+* T := Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp
    (algebraMap R B)) (by sorry) -- p は商で 0
  exact Under.mk (CommRingCat.ofHom (g.comp e.toRingHom))

def rootDeRhamAugmentation : SSet.Edge (rootDeRhamSource (E := E) (rootTestCoefficients p R hR))
    ((E.discrete _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (rootModPAlgebra p R hR))) := by
  sorry -- 要確認：A1-5 の自然性。X ↦ X_0、dX ↦ 0 の cdga 射

/-- 概要：de Rham 入力（A1-5、G-A5-15）：φ_A^*Δ_{T/A} ⊗^L_A A/(p,d) ≃ Ω^•_{(T/p)/(R/p)}（T = R⟨X⟩、E∞ 代数として）、T → T_∞ と両立し、
T_∞ 側は L_{T_∞/R}^∧ = 0 で T_∞/p。
方針：A1-5 の定理（Thm 6.4 の多項式・mod p の特別な場合）を引く。
規約：—
使われ方：(∗) への帰着。 -/
theorem rootMap_modP_eq_deRham :
    let f := reducedRootEdge (E := E) p R hR
    let g := rootDeRhamAugmentation (E := E) p R hR
    ∃ (l : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso _ (rootDeRhamSource (E := E) (rootTestCoefficients p R hR)))
      (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso _ ((E.discrete _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (rootModPAlgebra p R hR)))),
      SSet.Truncated.HomotopyCategory.homMk f.toTruncated ≫ r.hom =
        l.hom ≫ SSet.Truncated.HomotopyCategory.homMk g.toTruncated := by
  sorry -- 要確認：A1-5 の deRham_iso_polynomial_modP・deRham_iso_rootAlgebra_modP はまだ True。
        -- Frobenius 捻りを上の係数同型で移送し、T → T_∞ に対する自然性で四角形を得る

/-- 標準の Cartier 射。二項複体の次数 0 の環射は X ↦ X^p、
次数 1 の半線形写像は ε ↦ X^(p−1)dX。両辺とも次数 1 同士の積は零。 -/
def oneVariableCartierMap (C : Type u) [CommRing C] (hpC : (p : C) = 0) :
    let B := ModuleCat.of C (Polynomial C)
    let h : (ComplexShape.up ℕ).Rel 0 1 := rfl
    HomologicalComplex.double (0 : B ⟶ B) h ⟶
      HomologicalComplex.double (ModuleCat.ofHom (Polynomial.derivative (R := C))) h := by
  let h : (ComplexShape.up ℕ).Rel 0 1 := rfl
  let d := ModuleCat.ofHom (Polynomial.derivative (R := C))
  let i : Polynomial C →ₐ[C] Polynomial C := Polynomial.aeval (Polynomial.X ^ p)
  let m := LinearMap.mulLeft C (Polynomial.X ^ (p - 1) : Polynomial C)
  exact HomologicalComplex.mkHomFromDouble h (by decide)
    (ModuleCat.ofHom i.toLinearMap ≫ (HomologicalComplex.doubleXIso₀ d h).inv)
    (ModuleCat.ofHom (m.comp i.toLinearMap) ≫ (HomologicalComplex.doubleXIso₁ d h (by decide)).inv)
    (by sorry) (by sorry) -- d(X^p)=0、二次以上の成分は零

/-- 概要：G-A5-12：一変数 de Rham 複体の Cartier・形式性：任意の F_p 代数 R_0 で Ω^•_{R_0[X]/R_0} ≃ R_0[X^p] ⊕ R_0[X^p]·X^{p−1}dX[−1]
（零微分の分裂二乗零拡大）は cdga の擬同型（X^a R_0[X^p]、0 < a < p、の成分で d が同型）。
方針：Shared/DeRhamPolynomial の `deRhamComplex` の一変数版と直和分解。
規約：T := R_0[X^p] ≅ T^{(1)}。
使われ方：(∗)。 -/
theorem deRhamOneVariable_formal (C : Type u) [CommRing C] (hpC : (p : C) = 0) :
    let ι : Polynomial C →ₐ[C] Polynomial C := Polynomial.aeval (Polynomial.X ^ p)
    let ε : Polynomial C := Polynomial.X ^ (p - 1)
    QuasiIso (oneVariableCartierMap p C hpC) ∧
      (∀ b, Polynomial.derivative (ι b) = 0) ∧
      (∀ z : Polynomial C, Polynomial.derivative z = 0 → ∃! b, ι b = z) ∧
      (∀ z : Polynomial C, ∃! b, ∃ t : Polynomial C, z - ι b * ε = Polynomial.derivative t) := by
  sorry -- cdga 射は b↦ι b、bε↦ι(b)X^(p−1)dX（次数 1 同士の積は両側で零）。
        -- 三条件は鎖写像性、H⁰・H¹ の同型。指数を mod p に分解し非零剰余では微分が可逆

/-- 概要：G-A5-13 (∗)、**任意の離散 C 加群 L を係数に**（W9 続き 6）：Ω = B ⊕ Bε（B = C[X^p]、|ε| = 1、ε² = 0、微分 0）上、F_C ≅ B^{(J)}[−1]（T_∞/p は B 上自由で
1 を基底に含む）、Q := B ⊗_C L（B は C 上自由なので導来的にも離散）として RHom_Ω(N_C, Ω ⊗_C L) ≃ (∏ Q)[1] ∈ D^{≤−1}。L = C が元の (∗)。
方針：B の Ω 上の半自由分解 P（次数 0 の生成元 e_n、d(e_0) = 0、d(e_n) = εe_{n−1}）で Hom_Ω(P, Ω ⊗_C L) は次数 0・1 に ∏_n Q、微分は shift で核 0・余核 Q、
RHom_Ω(B, Ω ⊗_C L) ≃ Q[−1]；B ⊗^L_Ω B ≃ ⊕_n B は次数 0；F_C の二乗と shift を戻す。積は完全で L の平坦性は不要。
規約：D(Ω)。
使われ方：`rootMap_fiber_rhom_coconnective`。 -/
theorem squareZero_rhom_coconnective (L : ModuleCat.{u} (rootTestCoefficients p R hR)) :
    let C := rootTestCoefficients p R hR
    let Q := Polynomial C ⊗[C] L
    let J := {a : ℚ // 0 ≤ a ∧ a < p ∧ ∃ n : ℕ, ∃ m : ℕ, a = (m : ℚ) / p ^ n}
    let M := fiberSquareRHom (E := E) (reducedRootEdge (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex C L)
    Nonempty (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence C).functor.obj ⟨M⟩) ≅
      ((DerivedCategory.singleFunctor (ModuleCat C) (-1)).obj (ModuleCat.of C ((J × J × ℕ) → Q)))) ∧
      Derived.IsConnectiveAt C (-1) M := by
  sorry -- B=C[X^p] は多項式環。J は T_∞/p の B 基底、0 番目を Bε に替えて fib≃B^(J)[−1]。
        -- 半自由分解の shift の核は零、余核は Q。二つの J と分解の ℕ が積を添字付ける

/-- 概要：n = 1 の Lemma 8.6：上の五つを合わせる。
方針：—
規約：—
使われ方：`prismaticCohomology_rootMap_descendable`。 -/
theorem rootMap_descendable_one :
    HasDescentIndexLEOver (E := E) (perfectPrismRing p R) _ _ (deltaRootEdge (E := E) p R hR 1) 2 := by
  sorry -- rootMap_fiber_rhom_coconnective から Shared/Descendable の (f)
        -- hasDescentIndexLEOver_two_of_rhom 待ち。Lemma 8.6 の結論では index の数値は使わない

end SerrePositivity.BhattScholze.Perfectoidization.Derived
