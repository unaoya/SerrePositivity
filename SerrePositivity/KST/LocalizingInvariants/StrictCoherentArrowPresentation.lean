module

public import SerrePositivity.KST.LocalizingInvariants.StrictCoherentArrowTriangles
public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalHomotopy
public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeNormalization
public import SerrePositivity.KST.LocalizingInvariants.HomotopyMapTransport
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PrismHomotopy

/-!
概要：通常の自然変換の一つの射への制限を、元の二つの合成三角形の全 h Fun 合成で表す。
方針：元の正方形の対角分解に二単体の計算を渡し、自然性で共通対角の端点を揃える。
規約：自然変換の元の円柱を保持。使われ方：模型 cube の三因子の右辺表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.StrictArrow

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {F G : I ⥤ C} (η : F ⟶ G) {i j : I} (k : i ⟶ j)

def homotopy := stableHomotopyPrecomp (shape k)
  (F2.prismHomotopy (F2.strictCoherentNatTransMap η)
    (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _))

lemma homotopy_map : (homotopy η k).h = prism η k := by
  change (shape k ▷ (Δ[1] : SSet.{max u v})) ≫
    (β_ _ Δ[1]).hom ≫ F2.strictCoherentNatTransMap η = _
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc]
  rfl

def post := TriangleEdge.normalizedPost (coherentNerveCompStruct (F.map k) (η.app j)).simplex
  (coherentNerveEdge (F.map k)).edge (coherentNerveEdge (F.map k ≫ η.app j)).edge
  (coherentNerveCompStruct (F.map k) (η.app j)).d₂
  (coherentNerveCompStruct (F.map k) (η.app j)).d₁

def pre := HomotopyArrow.rebase
  (TriangleEdge.normalizedPre (coherentNerveCompStruct (η.app i) (G.map k)).simplex
    (coherentNerveEdge (η.app i ≫ G.map k)).edge (coherentNerveEdge (G.map k)).edge
    (coherentNerveCompStruct (η.app i) (G.map k)).d₁
    (coherentNerveCompStruct (η.app i) (G.map k)).d₀)
  (congrArg (fun r ↦ SSet.yonedaEquiv.symm (coherentNerveEdge r).edge) (η.naturality k).symm) rfl

lemma afterBottom_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (SquareDiagonal.afterBottom (homotopy η k)))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (post η k))) := by
  apply HomotopyArrow.congr
  have ht : squareTriangle 1 ≫ (homotopy η k).h =
      SSet.yonedaEquiv.symm (coherentNerveCompStruct (F.map k) (η.app j)).simplex := by
    exact (congrArg (fun r ↦ squareTriangle 1 ≫ r) (homotopy_map η k)).trans
      (SSet.yonedaEquiv.eq_symm_apply.mpr (lower η k))
  change SquareDiagonal.postShape ≫ squareTriangle 1 ≫ (homotopy η k).h = _
  rw [ht]
  rfl

lemma beforeTop_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (SquareDiagonal.beforeTop (homotopy η k)))) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (pre η k))) := by
  apply HomotopyArrow.congr
  have ht : squareTriangle 0 ≫ (homotopy η k).h =
      SSet.yonedaEquiv.symm (coherentNerveCompStruct (η.app i) (G.map k)).simplex := by
    exact (congrArg (fun r ↦ squareTriangle 0 ≫ r) (homotopy_map η k)).trans
      (SSet.yonedaEquiv.eq_symm_apply.mpr (upper η k))
  change _ = (HomotopyArrow.rebase _ _ _).h
  rw [HomotopyArrow.rebase_map]
  change SquareDiagonal.preShape ≫ squareTriangle 0 ≫ (homotopy η k).h = _
  rw [ht]
  rfl

lemma presentation :
    Arrow.mk (homPre (shape k) (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (F2.prismHomotopy (F2.strictCoherentNatTransMap η)
        (F2.strictCoherentNatTransMap_zero _) (F2.strictCoherentNatTransMap_one _))))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (post η k)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (pre η k))) := by
  unfold homPre
  rw [homMk_functorEdge_precomp]
  change Arrow.mk (Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (homotopy η k))) = _
  rw [SquareDiagonal.homMk_decomposition]
  exact arrow_mk_comp_congr (afterBottom_arrow η k) (beforeTop_arrow η k)

end SerrePositivity.KST.LocalizingInvariants.StrictArrow
