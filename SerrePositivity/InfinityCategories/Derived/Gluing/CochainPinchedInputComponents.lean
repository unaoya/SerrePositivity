module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaPinchedInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismCoefficientComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedChainMapComponent

/-! 実 cochain 入力の二射影・primitive を、元複体の同じ全線形成分で評価する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex
open DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
local notation "F" => dgGluingCochainIdentityCommaLift R E x y K f g h he
variable {n : ℕ} (s : (complexPinchedSpace.{u, max u v} K) _⦋n⦌)
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))

lemma dgGluingCochainPinchedInput_component :
    (toLinearData ((dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s)).component J k hJ hk =
      (F).f k ((complexUnitHomIso K).inv.f k ((toLinearData s).component J k hJ hk)) := by
  have hi : dgGluingCochainIdentityCommaPinchedInput.{u, v} R E x y K f g h he =
      pinchedHomChainMap
      (D := DGComplexPinchedModel.{u, max u v} K)
      (E := DGFunctorCommaObject R E E (DGFunctor.id E))
      (x := complexPinchedSource K) (y := complexPinchedTarget K)
      (x' := dgGluingIdentityCommaObject R E x) (y' := dgGluingIdentityCommaObject R E y)
      ((complexUnitHomIso K).inv ≫ F) :=
    dgGluingComplexPinchedInput_eq_chainMap.{u, max u v}
      (E := DGFunctorCommaObject R E E (DGFunctor.id E))
      (x := dgGluingIdentityCommaObject R E x) (y := dgGluingIdentityCommaObject R E y) F
  rw [hi]
  exact dgGluingPinchedChainMapSimplex_component.{u, max u v}
    (C := DGComplexPinchedModel.{u, max u v} K)
    (D := DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := complexPinchedSource K) (y := complexPinchedTarget K)
    (x' := dgGluingIdentityCommaObject R E x) (y' := dgGluingIdentityCommaObject R E y)
    ((complexUnitHomIso K).inv ≫ F) s J k hJ hk

lemma dgGluingCochainPinchedInput_source :
    dgGluingIdentityCommaSourceComponent R E ((dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s) J k hJ hk =
      g.f k ((complexUnitHomIso K).inv.f k ((toLinearData s).component J k hJ hk)) := by
  unfold dgGluingIdentityCommaSourceComponent
  rw [dgGluingCochainPinchedInput_component, dgGluingIdentityCommaTarget_map]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCochainIdentityCommaLift_end R E x y K f g h he) k) _

lemma dgGluingCochainPinchedInput_replacement :
    dgGluingIdentityCommaReplacementComponent R E ((dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s) J k hJ hk =
      f.f k ((complexUnitHomIso K).inv.f k ((toLinearData s).component J k hJ hk)) := by
  unfold dgGluingIdentityCommaReplacementComponent
  rw [dgGluingCochainPinchedInput_component]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (dgGluingCochainIdentityCommaLift_start R E x y K f g h he) k) _

lemma dgGluingCochainPinchedInput_primitive :
    dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) k
      ((toLinearData ((dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s)).component J k hJ hk) =
      (-h).v k (k - 1) (by omega)
        ((complexUnitHomIso K).inv.f k ((toLinearData s).component J k hJ hk)) := by
  unfold dgCommaAugmentationHomotopyComponent
  rw [dgGluingCochainPinchedInput_component]
  have hh := ConcreteCategory.congr_hom
    (Cochain.congr_v (dgGluingCochainIdentityCommaLift_primitive R E x y K f g h he)
      k (k - 1) (by omega))
    ((complexUnitHomIso K).inv.f k ((toLinearData s).component J k hJ hk))
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ModuleCat.comp_apply] at hh
  convert hh using 1

end SerrePositivity.InfinityCategories
