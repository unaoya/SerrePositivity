module
public import SerrePositivity.KST.SConstruction.ConnectedBaseChangeDetection

/-! # 切断を持つ基底射の往復引き戻し
概要：基底射をその切断に沿って戻した fiber 積は元の全空間と厳密に同型。
方針：二重 pullback の三座標を取り、切断の等式で余分な座標を消す。
規約：Kan 性・同値性は不要。使われ方：退化に沿って面比較を検出する際の標的。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet

/-- 切断に沿って戻した二重 pullback の二つの基底射影は一致する。 -/
lemma splitBasePullback_projection {E B B' : SSet.{u}} (p : E ⟶ B)
    (s : B ⟶ B') (t : B' ⟶ B) (hst : s ≫ t = 𝟙 B) :
    pullback.fst (pullback.fst t p) s ≫ pullback.snd t p ≫ p =
      pullback.snd (pullback.fst t p) s := by
  calc
    _ = pullback.fst (pullback.fst t p) s ≫ pullback.fst t p ≫ t := by
      rw [pullback.condition]
    _ = pullback.snd (pullback.fst t p) s ≫ s ≫ t := by
      rw [← Category.assoc, pullback.condition, Category.assoc]
    _ = _ := by rw [hst, Category.comp_id]

/-- 切断を持つ基底射の fiber 積をその切断へ戻すと元の全空間を厳密に回収する。 -/
def splitBasePullbackIso {E B B' : SSet.{u}} (p : E ⟶ B)
    (s : B ⟶ B') (t : B' ⟶ B) (hst : s ≫ t = 𝟙 B) :
    pullback (pullback.fst t p) s ≅ E where
  hom := pullback.fst (pullback.fst t p) s ≫ pullback.snd t p
  inv := pullback.lift (pullback.lift (p ≫ s) (𝟙 E) (by
    rw [Category.assoc, hst, Category.comp_id, Category.id_comp])) p
      (by rw [pullback.lift_fst])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
        have h := congrArg (fun f => f ≫ s) (splitBasePullback_projection p s t hst)
        simpa only [Category.assoc] using h.trans
          (pullback.condition (f := pullback.fst t p) (g := s)).symm
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      exact splitBasePullback_projection p s t hst
  inv_hom_id := by
    simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]

end SerrePositivity.KST.SConstruction
