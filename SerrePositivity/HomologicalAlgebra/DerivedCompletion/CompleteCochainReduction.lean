module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePower
public import SerrePositivity.CommutativeAlgebra.Adic.ReductionScalarExtension
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelEquivalence
import all SerrePositivity.CommutativeAlgebra.Koszul.Basic
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTower
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic

/-!
# 完備複体の通常商による零性の判定

## 概要
各項で正則なスカラーによる通常商が非輪状なら、導来完備な元の複体も非輪状になる。

## 方針
通常商とスカラー錐の擬同型を使い、完備ホモロジー上のスカラー作用の全射性を適用する。

## 規約
環上の正則性を仮定せず、複体の各項の作用に正則性を課す。

## 使われ方
BS 著者版 Theorem 6.4 の厳密な比較射を mod p から持ち上げる。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] (a : R)

/-- 通常商のホモロジーが零なら、完備な元の複体の同じ次数のホモロジーも零。 -/
theorem cochain_homology_isZero_of_complete_of_powerCokernel
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hc : IsComplete R a (DerivedCategory.Q.obj K))
    (hr : ∀ i, Function.Injective (fun x : K.X i => a • x)) (i : ℤ)
    (hq : IsZero ((powerCokernelComplex a K 1).homology i)) :
    IsZero (K.homology i) := by
  have hS := powerScalarCokernelShortExact a K hr 1
  have : QuasiIso (koszulPowerCokernelAugmentation a K 1) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let e := asIso (homologyMap (koszulPowerCokernelAugmentation a K 1) i)
  have hz : IsZero (((scalarConeFunctor a).obj K).homology i) := by
    simpa only [complexPowerKoszulStage, pow_one, scalarConeFunctor] using hq.of_iso e
  let eh := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeComparison R a).symm.app K)
  have h := derived_homology_isZero_of_complete_of_scalarCone_isZero a
    (DerivedCategory.Q.obj K) hc i (hz.of_iso eh.symm)
  exact h.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm

/-- スカラーによる通常商を、元の環の加群のまま扱う関手。 -/
def scalarReductionFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (AdicReduction (Ideal.span {a}) M)
  map f := ModuleCat.ofHom ((adicReductionMap (Ideal.span {a}) f.hom).restrictScalars R)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance scalarReductionFunctor_additive : (scalarReductionFunctor a).Additive where
  map_add {X Y} {f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

private def reductionProjection (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ ((scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)).obj K where
  f i := ModuleCat.ofHom (Ideal.span {a} • (⊤ : Submodule R (K.X i))).mkQ
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

private def reductionShortComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId a K) (reductionProjection a K) (by
    ext i x
    change (Ideal.span {a} • (⊤ : Submodule R (K.X i))).mkQ (a • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top)

private theorem reductionShortComplex_shortExact
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hr : ∀ i, Function.Injective (fun x : K.X i => a • x)) :
    (reductionShortComplex a K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (Ideal.span {a} • (⊤ : Submodule R (K.X i))).mkQ x = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := (mem_principal_pow_smul_top a 1 x).mp (by
      simpa only [pow_one] using hx')
    refine ⟨y, ?_⟩
    change a • y = x
    simpa only [pow_one] using hy
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : K.X i => a • x)
    exact hr i
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- 完備複体の通常スカラー商の零性は、元の複体の零性を検出する。 -/
theorem cochain_homology_isZero_of_complete_of_reduction
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hc : IsComplete R a (DerivedCategory.Q.obj K))
    (hr : ∀ i, Function.Injective (fun x : K.X i => a • x)) (i : ℤ)
    (hq : IsZero ((((scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)).obj K).homology i)) :
    IsZero (K.homology i) := by
  let S := reductionShortComplex a K
  have hS := reductionShortComplex_shortExact a K hr
  have : Epi S.g := hS.epi_g
  let e : cokernel (smulId a K) ≅ S.X₃ :=
    (cokernelIsCokernel (smulId a K)).coconePointUniqueUpToIso hS.exact.gIsCokernel
  have hz : IsZero ((cokernel (smulId a K)).homology i) :=
    hq.of_iso ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso e)
  apply cochain_homology_isZero_of_complete_of_powerCokernel a K hc hr i
  simpa only [powerCokernelComplex, pow_one] using hz

/-- 項ごとに正則な二つの完備複体の射は、通常スカラー商で擬同型を判定できる。 -/
theorem cochain_quasiIso_of_complete_of_reduction
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hK : IsComplete R a (DerivedCategory.Q.obj K))
    (hL : IsComplete R a (DerivedCategory.Q.obj L))
    (hrK : ∀ i, Function.Injective (fun x : K.X i => a • x))
    (hrL : ∀ i, Function.Injective (fun x : L.X i => a • x))
    (hf : QuasiIso (((scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  let F := (scalarReductionFunctor a).mapHomologicalComplex (.up ℤ)
  let C := CochainComplex.mappingCone f
  have hC := isComplete_Q_mappingCone R a f hK hL
  have hrC (i : ℤ) : Function.Injective (fun x : C.X i => a • x) := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _
    apply (e.toLinearEquiv.isSMulRegular_congr a).mpr
    intro x y h
    exact Prod.ext (hrK (i + 1) (congrArg Prod.fst h)) (hrL i (congrArg Prod.snd h))
  have hz : (CochainComplex.mappingCone (F.map f)).Acyclic :=
    (cochain_quasiIso_iff_cone_acyclic _).mp hf
  have hzF : (F.obj C).Acyclic := cochainAcyclic_of_iso hz
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (scalarReductionFunctor a)).symm
  apply (cochain_quasiIso_iff_cone_acyclic f).mpr
  intro i
  exact (exactAt_iff_isZero_homology C i).mpr
    (cochain_homology_isZero_of_complete_of_reduction a C hC hrC i (hzF i).isZero_homology)

end SerrePositivity.DerivedCompletion
