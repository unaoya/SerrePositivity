module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGInvertingBinaryAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedIdentity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorRestrictionFamilyIso
/-!
概要：商 Hom の全降下選択空間上の作用が、実恒等族を保つことを証明する。
方針：元の Hom への全体制限同型を実恒等族で評価し、任意の選択パラメータで展開する。
規約：元の実恒等一次単体と任意パラメータを保つ。使われ方：局所化延長の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
/-- 実恒等族における作用は、全降下選択空間上で標的の同じ実恒等族に同型。 -/
def dgInvertingUnitActionIso (K : SSet.{max u v}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x x F ≫
      (pre (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x))))).app _)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorRestrictionFamilyIso_of_eq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamily A D P x x F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map x x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomActionFamilyRestrictionIso A D P x x F)
    (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
  · exact (SSet.const_comp _ _).trans (congrArg (fun a => SSet.const (X := K) a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorPinchedMap_identityVertex (DGQuotient.inclusion A D P) x))
  · exact (SSet.const_comp _ _).trans (congrArg (fun a => SSet.const (X := K) a)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMap_identityVertex F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
/-- 任意の全選択パラメータ上で、実恒等族の作用は同じ関手圏の恒等射を表す。 -/
lemma dgInvertingUnitAction_id (K S : SSet.{max u v})
    (p : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomDescentSpace A D P x x F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomFamilyValue A D P x x F
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) p ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) = 𝟙 _ := by
  let g := SSet.const (X := K)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorFamilyIsoUncurry_const g (dgInvertingUnitActionIso A D P x F K) p
  have h : Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingHomFamilyValue A D P x x F
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) p)
      (SSet.const (X := K ⊗ S)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))))) :=
    ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H rfl (SSet.comp_const _ _)⟩
  exact ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr h).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedFamilyHom_identity (K := K ⊗ S) (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
