module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionCoefficientPoint

/-! # Kan 対象の等式による表示変更は、同じ指定点の分類射を輸送する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- Kan 対象の等式で移した点は、同じ等式同型による分類射の後合成。 -/
theorem pointedSpaceFiberPointHom_eq_transport {K L : KanObject.{u}} (h : K = L)
    (v : K.obj _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv K).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (congrArg spaceInfinityVertex h))).hom =
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv L).symm
      (Eq.mp (congrArg (fun T : KanObject.{u} => T.obj _⦋0⦌) h) v)) := by
  subst L
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rfl

end SerrePositivity.KST.Fibration
