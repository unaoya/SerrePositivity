module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellKanCone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingFibration
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovHomotopyPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks

/-!
概要：元の Postnikov 錐の cell 写像模型は、実空間値図式の極限である。
方針：元の class の次数全射性から写像の Kan fibration 性を得て、実 cospan 判定を使う。
規約：元の頂点・両脚の像を保持し、代数の ∞ 局所化との導来比較は別工程とする。
使われ方：Postnikov 拡大の全導来写像空間による普遍性の実模型側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory Opposite HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

set_option maxHeartbeats 800000 in -- 元の cell 写像関手で写した Postnikov 錐の底を同定する。
def postnikovCellKanCone_underlying_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (postnikovCellKanCone R A B n hn)) := by
  change IsLimit ((multiplicativeMappingFunctor R (cellResolution R A)).mapCone
    ((postnikovAlgebraPullbackCone R B n hn).whisker
      (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)))
  exact isLimitOfPreserves (multiplicativeMappingFunctor R (cellResolution R A))
    ((postnikovAlgebraPullback_isLimit R B n hn).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm)

lemma postnikovCellMappingClass_fibration :
    Fibration (multiplicativeMappingPostcompose R (cellResolution R A)
      (postnikovPerturbedClass R B n hn)) := by
  apply multiplicativeCellMapping_fibration
  have := postnikovPerturbedClass_epi R B n hn
  intro k
  exact (ModuleCat.epi_iff_surjective _).mp (inferInstance :
    Epi ((postnikovPerturbedClass R B n hn).hom.f k))

set_option maxHeartbeats 800000 in -- 実 class の全 Hom と元の空間値錐の表示を照合する。
lemma postnikovCellSpaceCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovCellSpaceCone R A B n hn) := by
  have : Fibration
      (show ((multiplicativeCellMappingKanFunctor R A).obj
          (postnikovPerturbedExtension R B n hn)).obj ⟶
        ((multiplicativeCellMappingKanFunctor R A).obj
          (postnikovDerivationTarget R B n hn)).obj from
        (multiplicativeCellMappingKanFunctor R A).map (postnikovPerturbedClass R B n hn)) :=
    postnikovCellMappingClass_fibration R A B n hn
  have : ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (postnikovCellKanDiagram R A B n hn) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun Z => by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj (op Z)).map
      ((multiplicativeCellMappingKanFunctor R A).map (postnikovPerturbedClass R B n hn)))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration Z _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (postnikovCellKanCone R A B n hn)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (postnikovCellKanCone_underlying_isLimit R A B n hn))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
