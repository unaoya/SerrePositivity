module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeHomSourceSpaceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
/-!
概要：同じ二入力導来 Hom の基礎空間を、固定入力で元の F1 Hom∞ へ比較する。
方針：D(R) 値の全関手比較を同じ基礎空間へ送り、既存の両側の分類比較へ接続する。
規約：同じ tensor nerve の制限上の全関手比較。元の直積上の同定は別工程。
使われ方：二変数導来 Hom と元の写像空間関手の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite MonoidalCategory SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ二入力 D(R) 値 Hom の全基礎空間関手。 -/
def dgSemifreeDerivedHomTensorSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGTensorCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D))) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensorInfinity R D) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D
/-- 同じ固定始域制限は、元の F1 共変 Hom∞ と全関手同型。 -/
def dgSemifreeDerivedHomTensor_targetF1SpaceIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P))) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetF1SpaceInfinity R D P) := by
  have e := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensor_targetIso R D P).ulift).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D)
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeSecond R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (_root_.Opposite.op P))) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P) := by
    simpa only [dgSemifreeDerivedHomTensorSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetF1SpaceIso R D P
/-- 同じ固定終域制限は、実反対 ∞ 圏上の元の表現可能前層と全関手同型。 -/
def dgSemifreeDerivedHomTensor_sourceF1SpaceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q)) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTensor_sourceIso R D Q).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom
  have e := h.ulift.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D)
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorIncludeFirst R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) Q)) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity R D Q) := by
    simpa only [dgSemifreeDerivedHomTensorSpaceInfinity,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantF1SpaceIso R D Q
end SerrePositivity.InfinityCategories.Project.DerivedCategories
