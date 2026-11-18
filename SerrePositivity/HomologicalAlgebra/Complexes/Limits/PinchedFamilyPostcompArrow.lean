module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceIntervalNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.IntervalFamilyFunctorPrecomposition
/-! 概要：元の全 pinched 族を同じ導来 roof に同定する。
方針：全関手圏内の評価三角形と元の augmentation 逆を同じ関手で送る。
規約：全 K と端点輸送を保持。使われ方：標準単位比較自身の全高次比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
private lemma arrow_transport_eq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) :
    Arrow.mk (eqToHom hx.symm ≫ f ≫ eqToHom hy) = Arrow.mk f := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma pinchedFamilyPostcomp_arrow {K C D : SSet.{u}} (F : C ⟶ D)
    {x y : C _⦋0⦌} (p : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := D)
        (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))) =
      Arrow.mk ((hoFunctor.map ((ihom K).map F)).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomToIntervalMappingSpace_naturality, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso
  exact _root_.SerrePositivity.ComplexLimits.arrow_transport_eq
    (congrArg (fun H : K ⟶ D => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H))
      (SSet.const_comp x F))
    (congrArg (fun H : K ⟶ D => SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H))
      (SSet.const_comp y F)) _

end SerrePositivity.ComplexLimits
