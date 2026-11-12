module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CosliceTransportIntervalComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedComposition

/-!
概要：元の coslice fiber の右写像空間への比較は、指定辺の標準後合成に全自然。
方針：同じ輸送と区間比較のホモトピーを、指定した右模型への逆で移す。
規約：既存の cosliceFiberRightMappingEquivalence の順射を保持する。
使われ方：G8 の表現可能値の同じ比較の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：同じ coslice の輸送と、元の右写像空間比較による標準後合成の可逆二胞体。
方針：区間族の同型を右比較の逆で戻し、中間の逆と順射を相殺する。
規約：全 fiber をパラメータにし、必要な同型を仮定しない。
使われ方：表現可能値の標準後合成の比較。 -/
def cosliceTransport_rightMappingIso {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {c d : X _⦋0⦌} (e : X.Edge c d) :
    FunctorIso
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
        (cosliceFiberRightMappingEquivalence x d).hom)
      ((cosliceFiberRightMappingEquivalence x c).hom ≫
        postcompose x (SSet.Truncated.HomotopyCategory.homMk e)) := by
  let a := (pinchedHomToIntervalMappingSpace_isQCatEquivalence x c).choose
  let b := (pinchedHomToIntervalMappingSpace_isQCatEquivalence x d).choose
  let g := intervalPostcompose x (SSet.Truncated.HomotopyCategory.homMk e)
  have h := FunctorIso.postcomp
    (functorIsoOfSimplicialHomotopy (cosliceTransport_interval_homotopy x e).some) b.inv
  have k := FunctorIso.postcomp
    (FunctorIso.precomp a.invHomIso (cosliceFiberToIntervalMappingSpace x c)) (g ≫ b.inv)
  have hl : FunctorIso
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
        (cosliceFiberRightMappingEquivalence x d).hom)
      (cosliceFiberToIntervalMappingSpace x c ≫ g ≫ b.inv) := by
    simpa only [b, g, cosliceFiberRightMappingEquivalence, QCatEquivalence.trans,
      QCatEquivalence.symm, IsQCatEquivalence.choose, Category.assoc] using h
  have hr : FunctorIso
      ((cosliceFiberRightMappingEquivalence x c).hom ≫
        postcompose x (SSet.Truncated.HomotopyCategory.homMk e))
      (cosliceFiberToIntervalMappingSpace x c ≫ g ≫ b.inv) := by
    simpa only [a, b, g, cosliceFiberRightMappingEquivalence, postcompose, liftMap,
      QCatEquivalence.trans, QCatEquivalence.symm, IsQCatEquivalence.choose,
      Category.assoc, Category.id_comp, Category.comp_id] using k
  exact hl ≪≫ hr.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
