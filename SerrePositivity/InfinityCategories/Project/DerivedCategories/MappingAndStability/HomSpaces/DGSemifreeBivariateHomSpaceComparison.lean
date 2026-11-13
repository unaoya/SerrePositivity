module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGSemifreeBivariateHomSourceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSemifreeHomTensorSpaceComparison
/-!
概要：元の実直積上の二変数 Hom の基礎空間を、両固定入力で元の F1 Hom∞ と比較する。
方針：同じ D(R) 値の全関手同型を基礎空間へ送り、既存の分類比較と合成する。
規約：全単体・全面・退化を保つ。使われ方：二変数 D(R) 値 Hom の c5 の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 元の二変数 Hom の固定入力制限を F1 の同じ全関手へ比較する。 -/
def dgSemifreeDerivedHomBivariateSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariateInfinity R D) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D
/-- 元の二変数 Hom の固定入力制限を F1 の同じ全関手へ比較する。 -/
def dgSemifreeDerivedHomBivariate_targetF1SpaceIso (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (lift (SSet.const (SSet.opObjEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)))
          (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))) ≫
            dgSemifreeDerivedHomBivariateSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetF1SpaceInfinity R D P) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariate_targetIso R D P).ulift.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D)
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (lift (SSet.const (SSet.opObjEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)))
          (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D))) ≫
            dgSemifreeDerivedHomBivariateSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity R D P) := by
    simpa only [dgSemifreeDerivedHomBivariateSpaceInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetSpaceInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetF1SpaceIso R D P
/-- 元の二変数 Hom の固定入力制限を F1 の同じ全関手へ比較する。 -/
def dgSemifreeDerivedHomBivariate_sourceF1SpaceIso (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op)
          (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q))) ≫
            dgSemifreeDerivedHomBivariateSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomVertex R D Q)) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomBivariate_sourceIso R D Q).ulift.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedSpaceInfinity R D)
  have e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (lift (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op)
          (SSet.const (Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Q))) ≫
            dgSemifreeDerivedHomBivariateSpaceInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity R D Q) := by
    simpa only [dgSemifreeDerivedHomBivariateSpaceInfinity,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantSpaceInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomContravariantF1SpaceIso R D Q

end SerrePositivity.InfinityCategories.Project.DerivedCategories
