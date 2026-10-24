module

public import SerrePositivity.InfinityCategories.F2.Ind.LiftedShapeCosliceCocone
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCommaComparison

/-!
概要：元の下方余錐を厳密に持ち上げる関手では、指定変換を含む実 under comma に余錐がある。
方針：下方の coslice で全余錐を作り、その元の像を固定して持ち上げる。
規約：元の試験族と指定変換の両方を全射の等号で保持する。
使われ方：余錐図式から下方図式への制限の共終性と、旧頂点評価への伝播。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：指定像の余錐の厳密な持ち上げは、元の実 under comma の全余錐を与える。
方針：下方 coslice の全余錐を同じ射影で持ち上げる。規約：元の全族。使われ方：共終性。 -/
lemma nonempty_relativeComma_cocone_of_cocone_lifts
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {X Y : SSet.{u + 1}} (F : X ⟶ Y)
    (hY : ∀ {B : SSet.{u}}, IsKappaSmall κ B →
      ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ Y, Nonempty (JoinCocone f))
    (hF : ∀ {B : SSet.{u}}, IsKappaSmall κ B →
      ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X,
      ∀ G : JoinCocone (f ≫ F), ∃ c : JoinCocone f, mapJoinCocone F c = G)
    {A L : SSet.{u}} (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ Y)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ X)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ F = t ≫ sliceUnderProjection z) :
    Nonempty (JoinCocone (relativeCommaFamily F z t q ht)) := by
  obtain ⟨cT⟩ := nonempty_coslice_cocone_liftedShape_of_cocones hY hA hL z t
  let G : JoinCocone (q ≫ F) := ⟨cT.val ≫ sliceUnderProjection z, by
    rw [← Category.assoc, cT.property]
    exact ht.symm⟩
  obtain ⟨c, hc⟩ := hF hA q G
  have he : c.val ≫ F = cT.val ≫ sliceUnderProjection z := congrArg Subtype.val hc
  let U := relativeCommaFamily F z cT.val c.val he
  have hU : joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ≫ U =
      relativeCommaFamily F z t q ht := by
    apply pullback.hom_ext
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_fst]
      exact cT.property
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_snd]
      exact c.property
  exact ⟨⟨U, hU⟩⟩
end SerrePositivity.InfinityCategories.F2.Ind
