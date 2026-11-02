module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFaces

/-!
概要：元の全 Hom 係数で作った pointed 単体の実際の面を、coslice の座標で同定する。
方針：join 同型の自然性を使い、拡張単体の面の厳密な等式を反映する。
規約：全単体の等式であり、頂点や辺の類だけの同定ではない。
使われ方：元の三つの比較を同じ pointed 四面体の面へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の join 図式の面の座標を、元の一つ上の単体の面へ移す。 -/
lemma pointedSimplexCoordinates_face {X : SSet.{u}} {n : ℕ}
    (f : join Δ[0] Δ[n + 1] ⟶ X) (i : Fin (n + 2)) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      (joinMap (𝟙 Δ[0]) (stdSimplex.δ i) ≫ f)) =
        X.δ i.succ (SSet.yonedaEquiv ((leftPointStdSimplexIso (n + 1)).inv ≫ f)) := by
  erw [← Category.assoc,
    ← leftPointStdSimplexIso_inv_naturality (SimplexCategory.δ i),
    Category.assoc, ← SSet.yonedaEquiv_naturality, prependOrderHom_delta]
  rfl

/-- 実 pointed 単体の join 座標は、構成した同じ全拡張単体そのもの。 -/
lemma spaceSimplexPointedLift_coordinates {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
    (p : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      (spaceSimplexPointedLift s p).val) = spaceSimplexPointedAugmentation s p := by
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((leftPointStdSimplexIso n).hom ≫
      SSet.yonedaEquiv.symm (spaceSimplexPointedAugmentation s p))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- 全ての実 pointed 面の座標は、同じ拡張単体の対応する面。 -/
lemma spaceSimplexPointedLift_face_coordinates {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (p : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) (i : Fin (n + 2)) :
    SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
      (PointedSpaceInfinity.δ i (spaceSimplexPointedLift s p)).val) =
        SpaceInfinity.δ i.succ (spaceSimplexPointedAugmentation s p) := by
  exact (pointedSimplexCoordinates_face (spaceSimplexPointedLift s p).val i).trans
    (congrArg (fun t => SpaceInfinity.δ i.succ t)
      (spaceSimplexPointedLift_coordinates s p))

/-- 初点を残す面では、元の面の pointed 持ち上げを全単体として回収する。 -/
lemma spaceSimplexPointedLift_positive_face {n : ℕ}
    (s : SpaceInfinity.{u} _⦋n + 1⦌)
    (p : (Δ[n + 1] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) (i : Fin (n + 1)) :
    PointedSpaceInfinity.δ i.succ (spaceSimplexPointedLift s p) =
      spaceSimplexPointedLift (SpaceInfinity.δ i.succ s)
        (stdSimplex.δ i.succ ≫ p) := by
  apply Subtype.ext
  apply (cancel_epi (leftPointStdSimplexIso n).inv).mp
  apply SSet.yonedaEquiv.injective
  rw [spaceSimplexPointedLift_face_coordinates, spaceSimplexPointedLift_coordinates,
    spaceSimplexPointedAugmentation_positive_face]

end SerrePositivity.InfinityCategories.F2
