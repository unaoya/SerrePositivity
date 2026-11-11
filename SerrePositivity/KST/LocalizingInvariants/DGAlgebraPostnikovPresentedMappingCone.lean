module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLargeSpaceLimit
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeCoherent

/-!
概要：元の dg 代数の局所化提示の錐を、大宇宙の実 cell 写像錐と全図式で照合する。
方針：元の ULiftHom 表示からの回収を関手等式として使い、錐の頂点と全ての脚を保持する。
規約：元の代数の ∞ 局所化後の極限性や導来比較を仮定しない。
使われ方：実写像模型の極限性を、指定された元の Postnikov 錐へ接続する準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovPresentedCellMappingDiagram :
    postnikovInfinityCospan R B n hn ⋙ multiplicativeCellMappingInfinityKanFunctor R A =
      postnikovCellLargeKanDiagram R A B n hn := by
  change (_ ⋙ infinityPresentationFunctor R) ⋙
    multiplicativeCellMappingInfinityKanFunctor R A = _
  rw [Functor.assoc, multiplicativeCellMappingInfinityKanFunctor_original]
  rfl

lemma postnikovPresentedCellMappingCoherentDiagram :
    SSet.uliftFunctor.{u + 2, u + 1}.map (nerveMap (postnikovInfinityCospan R B n hn)) ≫
        multiplicativeCellMappingInfinityCoherent R A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (postnikovCellLargeKanDiagram R A B n hn) := by
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (multiplicativeCellMappingInfinityKanFunctor R A) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_precomp, postnikovPresentedCellMappingDiagram]

set_option maxHeartbeats 800000 in -- 元の提示錐と cell 写像錐の型の表示を照合する。
def postnikovPresentedCellMappingCone : Cone (postnikovCellLargeKanDiagram R A B n hn) :=
  (Cone.postcompose (eqToHom (postnikovPresentedCellMappingDiagram R A B n hn))).obj
    ((multiplicativeCellMappingInfinityKanFunctor R A).mapCone
      (postnikovInfinityPresentedCone R B n hn))

set_option maxHeartbeats 800000 in -- 提示の厳密な回収により元の全ての脚を同定する。
def postnikovPresentedCellMappingConeIso :
    postnikovPresentedCellMappingCone R A B n hn ≅ postnikovCellLargeKanCone R A B n hn := by
  refine Cone.ext (Iso.refl _) ?_
  intro j
  simp only [Iso.refl_hom, Category.id_comp]
  change _ ≫ (eqToHom (postnikovPresentedCellMappingDiagram R A B n hn)).app j = _
  simp only [eqToHom_app]
  rfl

set_option maxHeartbeats 800000 in -- 元の提示の錐へ全図式同型で極限の普遍性を戻す。
def postnikovPresentedCellMappingCone_isLimit :
    IsLimit (postnikovPresentedCellMappingCone R A B n hn) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCone_isLimit_of_forget _
    (postnikovCellLargeKanCone_underlying_isLimit R A B n hn)).ofIsoLimit
      (postnikovPresentedCellMappingConeIso R A B n hn).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
