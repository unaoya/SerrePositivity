module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PushoutTopMappingFiber
public import SerrePositivity.InfinityCategories.F1.SpanCoconeMappingPullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.VertexFiberIsPullbackIso

/-!
概要：pushout の右枝上の指定 fiber を、左枝の始点制限の指定 fiber に同定する。
方針：span の余錐空間の厳密な引き戻しを、右枝の図式表示の同型で移す。
規約：固定終点と指定右枝余錐を保持し、元の左枝の全空間に結論する。
使われ方：HTT 5.5.5.13 の元の二辺に対する fiber の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)

/-- 入力 span の右枝は、元の四角形の左辺そのもの。 -/
lemma pushoutSpan_rightDiagram : horn₂₀.ι₀₂ ≫ pushoutSpan R = squareLeftEdge ≫ R := by
  rw [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]

/-- 元の右枝余錐を、入力 span の左枝の始点に制限する。 -/
def pushoutSpanRightBase (y : C _⦋0⦌) :
    coconeMappingSpace (squareLeftEdge ≫ R) y ⟶
      coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ ≫ pushoutSpan R) y :=
  (cosliceFiberDiagramIso (pushoutSpan_rightDiagram R) y).inv ≫
    spanCoconeMappingRightBase (pushoutSpan R) y

/-- 元の同じ図式の表示で、span の余錐空間は依然として厳密な引き戻しとなる。 -/
lemma pushoutSpanMapping_isPullback (y : C _⦋0⦌) :
    IsPullback (cosliceRestrictionFiberMap (pushoutSpan R) horn₂₀.ι₀₁ y)
      (pushoutSpanRightMappingRestriction R y)
      (cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ pushoutSpan R) (stdSimplex.δ (1 : Fin 2)) y)
      (pushoutSpanRightBase R y) := by
  let e := cosliceFiberDiagramIso (pushoutSpan_rightDiagram R) y
  apply (spanCoconeMapping_isPullback (pushoutSpan R) y).of_iso
    (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, pushoutSpanRightMappingRestriction,
      normalizedCoconeRestrictionFiber_eq, e, cosliceFiberDiagramIso, eqToIso.hom]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, pushoutSpanRightBase, e,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 右枝上の同じ指定 fiber は、元の左枝の始点制限の同じ fiber と厳密に同型。 -/
def pushoutSpanSourceFiberIso (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    vertexFiber (pushoutSpanRightMappingRestriction R y) d ≅
      vertexFiber (cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ pushoutSpan R)
        (stdSimplex.δ (1 : Fin 2)) y) ((pushoutSpanRightBase R y).app _ d) :=
  vertexFiberIsoOfIsPullback (pushoutSpanMapping_isPullback R y) d

/-- 元の左枝の指定 fiber の可縮性は、上辺の指定 fiber の可縮性と一致する。 -/
lemma pushoutSourceFiber_contractible_iff [Quasicategory C]
    (hR : IsPushoutSquare R) (y : C _⦋0⦌)
    (d : (coconeMappingSpace (squareLeftEdge ≫ R) y) _⦋0⦌) :
    IsContractibleKan (vertexFiber (cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ pushoutSpan R)
      (stdSimplex.δ (1 : Fin 2)) y) ((pushoutSpanRightBase R y).app _ d)) ↔
      IsContractibleKan (vertexFiber (squareTopSourceMappingRestriction R y)
        ((cosliceRestrictionFiberMap (squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y).app _ d)) := by
  constructor
  · intro h
    exact (pushoutMappingFiber_contractible_iff R hR y d).mp
      (isContractibleKan_of_iso (pushoutSpanSourceFiberIso R y d).symm h)
  · intro h
    exact isContractibleKan_of_iso (pushoutSpanSourceFiberIso R y d)
      ((pushoutMappingFiber_contractible_iff R hR y d).mpr h)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
