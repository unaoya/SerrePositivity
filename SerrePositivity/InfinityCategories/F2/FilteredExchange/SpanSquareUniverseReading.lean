module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SquareFamilyReading
public import SerrePositivity.InfinityCategories.Stable.UniverseUniversalSquares

/-!
概要：小さい span 全余錐の宇宙持ち上げを、その同じ元の実四角形へ読み戻す。
方針：普遍四角形の既存の宇宙整合性を、正方形同型の逆向きへ移す。
規約：極限性を仮定しない、全写像の厳密な等式。
使われ方：Ind Yoneda の全余錐族の各段を、元の C の実四角形に照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 小さい span の持ち上げた余錐と、大きい宇宙の元の正方形の実同型。 -/
def uliftSpanSquareReadingIso :
    join ((SSet.uliftFunctor.{v, u}).obj (horn 2 0)) (Δ[0] : SSet.{max u v}) ≅
      (Δ[1] : SSet.{max u v}) ⊗ Δ[1] :=
  joinIso (uliftHornIso.{u, v} 2 0) (Iso.refl Δ[0]) ≪≫ spanCoconeSquareIso

/-- 元の全余錐を持ち上げて四角形へ読むことは、元の四角形を持ち上げることと一致する。 -/
lemma uliftCoconeSquareReading {X : SSet.{u}} {p : (horn 2 0 : SSet.{u}) ⟶ X}
    (c : JoinCocone p) :
    (uliftSpanSquareReadingIso.{u, v}).inv ≫ (JoinCocone.ulift.{u, v} c).val =
      uliftSquare.{u, v} (coconeSquare c) := by
  have h := pushoutCocone_ulift_reindex_val.{u, v} (coconeSquare c)
  have hv : (pushoutCocone (coconeSquare c)).val = c.val := by
    change spanCoconeSquareIso.hom ≫ (spanCoconeSquareIso.inv ≫ c.val) = c.val
    rw [Iso.hom_inv_id_assoc]
  change joinMap (uliftHornIso.{u, v} 2 0).inv (𝟙 Δ[0]) ≫
    ((uliftCoconeShapeIso.{u, v} (horn 2 0 : SSet.{u}) 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (pushoutCocone (coconeSquare c)).val) =
    spanCoconeSquareIso.hom ≫ uliftSquare (coconeSquare c) at h
  rw [hv] at h
  change joinMap (uliftHornIso.{u, v} 2 0).inv (𝟙 Δ[0]) ≫
    (JoinCocone.ulift.{u, v} c).val =
      spanCoconeSquareIso.hom ≫ uliftSquare (coconeSquare c) at h
  apply (cancel_epi spanCoconeSquareIso.hom).mp
  simpa only [uliftSpanSquareReadingIso, Iso.trans_inv, joinIso, Iso.refl_inv,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h

end SerrePositivity.InfinityCategories.F2
