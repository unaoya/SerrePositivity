module
public import SerrePositivity.KST.SConstruction.ArTwoExtension
public import SerrePositivity.KST.SConstruction.CofiberCompletion
public import SerrePositivity.KST.SConstruction.CofiberRows
public import SerrePositivity.KST.SConstruction.FrameBoundaryExtension

/-! # S₂ から cofiber 正方形への制限
概要：gapped Ar[2] 図式を中央の cofiber 正方形に制限する。
方針：零角と押し出し条件を全部分複体へ移し、外側の零対角の延長を使う。
規約：選択した零対象に置き換えない。使われ方：McCarthy 加法性の正方形表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped Ar[2] 図式の中央は cofiber 正方形。
方針：三つ組 (0,1,2) の零角と押し出し条件。
規約：元の四角形を保持する。使われ方：全部分複体への制限。 -/
lemma isGapped_two_middle {C : SSet.{u}} {F : arNerve 2 ⟶ C} (hF : IsGapped F) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (arTwoMiddleSquare ≫ F) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arTwoMiddleSquare ≫ F) := by
  refine ⟨?_, hF.2 0 1 1 2 (by decide) le_rfl (by decide)⟩
  rw [arTwoMiddleSquare, arSquare_cofiber_zero_corner]
  exact hF.1 1

/-- 概要：S₂ から cofiber 正方形全体への制限。
方針：中央正方形への前合成を cofiber の全部分複体へ持ち上げる。
規約：高次の自然変換も制限する。使われ方：McCarthy の正方形表示への比較。 -/
def sTwoCofiberRestriction (C : SSet.{u}) : sConstruction 2 C ⟶ cofiberDiagrams C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift IsCofiberDiagramVertex
    ((gappedSubcomplex 2 C).ι ≫ (pre arTwoMiddleSquare).app C) (by
      intro v
      let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve 2) C).symm v.val
      have hF : IsGapped F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
      change IsCofiberDiagramVertex (((pre arTwoMiddleSquare).app C).app (Opposite.op ⦋0⦌) v.val)
      rw [← hv]
      change IsCofiberDiagramVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arTwoMiddleSquare ≫ F))
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (arTwoMiddleSquare ≫ F))) 0 1) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C (arTwoMiddleSquare ≫ F)))
      rw [Equiv.symm_apply_apply]
      exact isGapped_two_middle hF)

/-- 概要：制限の実際の四角形は中央正方形への前合成。
方針：全部分複体への持ち上げの包含の式。
規約：全単体での厳密等号。使われ方：境界持ち上げの可換性。 -/
lemma sTwoCofiberRestriction_ι (C : SSet.{u}) :
    sTwoCofiberRestriction C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι =
      (gappedSubcomplex 2 C).ι ≫ (pre arTwoMiddleSquare).app C := rfl

/-- 概要：中央正方形への制限は頂点で全射。
方針：指定した cofiber 正方形の外側に零対角を補う。
規約：標的は quasicategory のみで安定性は不要。使われ方：境界持ち上げの零次元。 -/
lemma sTwoCofiberRestriction_vertex_surjective (C : SSet.{u}) [Quasicategory C] :
    Function.Surjective ((sTwoCofiberRestriction C).app (Opposite.op ⦋0⦌)) := by
  intro v
  let R := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram v.val
  have hv : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex R 0 1) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  obtain ⟨F, hF, he⟩ := exists_gapped_arTwo_of_cofiber (⟨R, hv.1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle C) hv.2
  let w : (sConstruction 2 C) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C F))
    rw [Equiv.symm_apply_apply]
    exact hF⟩
  refine ⟨w, Subtype.ext ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arTwoMiddleSquare ≫ F) = v.val
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _

end SerrePositivity.KST.SConstruction
