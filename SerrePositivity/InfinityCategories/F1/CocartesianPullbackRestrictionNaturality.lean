module

public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativePre

/-!
概要：元の全 cocartesian Hom の底変換への制限は、底上の射に関して自然。
方針：全パラメーターの作用を展開し、pullback の射影の自然性で比較する。
規約：元の標的へ写す局所 Hom と両射影を底変換した Hom の双方で厳密に可換。
使われ方：元の全相対 Hom の core の降下を各底変換の元の Hom へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
  {a b : Over B} (f : a ⟶ b)

/-- 元の全 Hom の局所 Hom への制限は、底上の射による前合成と厳密に可換。 -/
lemma cocartesianPullbackHomRestriction_naturality :
    cocartesianPullbackHomRestriction p q b ≫ cocartesianPullbackHomPre p q f =
      cocartesianPullbackHomRestriction p q a := by
  apply markedCocartesianFunctorUncurry_injective
  unfold cocartesianPullbackHomPre
  refine (markedCocartesianFunctorUncurry_overPre q
    ((Over.pullback p ⋙ Over.map p).map f)
    {e | IsCocartesianEdge (pullback.fst a.hom p) e}
    {e | IsCocartesianEdge (pullback.fst b.hom p) e}
    (fun e he ↦ isCocartesianEdge_overPullback_map p f e he)
    (cocartesianPullbackHomRestriction p q b)).trans ?_
  unfold cocartesianPullbackHomRestriction
  have h (c : Over B) := markedCocartesianFunctorUncurry_overPre q
    (Over.homMk (U := Over.mk (pullback.snd c.hom p ≫ p)) (V := Over.mk p)
      (pullback.snd c.hom p) rfl)
    {e | IsCocartesianEdge (pullback.fst c.hom p) e} {e | IsCocartesianEdge p e}
    (fun e he ↦ (isCocartesianEdge_overPullback_iff p c e).mp he)
    (𝟙 (cocartesianRelativeFunctorSpace p q))
  simp only [Category.id_comp] at h
  rw [h b, h a]
  change (((overPullbackUnderlying p).map f) ▷ _) ≫
    (pullback.snd b.hom p ▷ _) ≫ _ = (pullback.snd a.hom p ▷ _) ≫ _
  rw [← Category.assoc, ← comp_whiskerRight, overPullbackUnderlying_map_snd]

/-- 元の全 Hom の各底変換の元の Hom への制限も、底上の射に関して厳密に自然。 -/
lemma cocartesianPullbackNativeRestriction_naturality :
    cocartesianPullbackNativeRestriction p q b ≫ cocartesianPullbackNativePre p q f =
      cocartesianPullbackNativeRestriction p q a := by
  apply (cancel_mono (cocartesianPullbackHomIso p q a).hom).mp
  rw [Category.assoc, cocartesianPullbackNativePre_iso, ← Category.assoc,
    cocartesianPullbackNativeRestriction_iso, cocartesianPullbackHomRestriction_naturality,
    cocartesianPullbackNativeRestriction_iso]

end SerrePositivity.InfinityCategories
