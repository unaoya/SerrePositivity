module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaPinchedInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.IdentityCommaPrismCoefficientComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.PinchedChainMapComponent

/-! 実 cochain 入力の二射影・primitive を、元複体の同じ全線形成分で評価する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory HomologicalComplex DifferentialGraded CochainComplex HomComplex

open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (x y : E)
  (K : _root_.SerrePositivity.DifferentialGraded.Complex R) (f g : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y)
  (h : Cochain K (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he
variable {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) _⦋n⦌)
  (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))

lemma dgGluingCochainPinchedInput_component :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s)).component J k hJ hk =
      (F).f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v} R E x y K f g h he =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
      (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} K)
      (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
      (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ F) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap.{u, max u v}
      (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) F
  rw [hi]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedChainMapSimplex_component.{u, max u v}
    (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} K)
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource K) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget K)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ F) s J k hJ hk

lemma dgGluingCochainPinchedInput_source :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s) J k hJ hk =
      g.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaSourceComponent
  rw [dgGluingCochainPinchedInput_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaTarget_map]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_end R E x y K f g h he) k) _

lemma dgGluingCochainPinchedInput_replacement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent R E ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s) J k hJ hk =
      f.f k ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaReplacementComponent
  rw [dgGluingCochainPinchedInput_component]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start R E x y K f g h he) k) _

lemma dgGluingCochainPinchedInput_primitive :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) k
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, v}
      R E x y K f g h he).app (Opposite.op ⦋n⦌) s)).component J k hJ hk) =
      (-h).v k (k - 1) (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent
  rw [dgGluingCochainPinchedInput_component]
  have hh := ConcreteCategory.congr_hom
    (Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_primitive R E x y K f g h he)
      k (k - 1) (by omega))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv.f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s).component J k hJ hk))
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ModuleCat.comp_apply] at hh
  convert hh using 1

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
