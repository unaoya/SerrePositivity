module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeCoconeCommonExtension
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaKappaCocone
public import SerrePositivity.InfinityCategories.F2.Ind.SmallPushout
public import SerrePositivity.InfinityCategories.F1.Universe.Pushouts
/-!
概要：元の scalar Ind comma の小さい全図式に、指定部分上の下側変換を加えた余錐を作る。
方針：単射に沿う小さい pushout で全図式を貼り、共同余錐の二つの制限を回収する。
規約：元の全族と指定変換を保持し、二余錐の射影を厳密に照合する。
使われ方：終点評価下での補間拡張の選び直し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：指定部分上の下側変換を、同じ元の全図式の余錐と同時に延長できる。
方針：κ-small な共同図式の余錐を使う。
規約：元の射と指定値を保持。使われ方：終点評価の相対余錐。 -/
lemma exists_indComma_relative_cocones
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {C A B L : SSet.{u}} [Quasicategory C]
    (x : (IndInfinity κ C) _⦋0⦌) (i : A ⟶ B) [Mono i]
    (hA : IsKappaSmall κ A) (hB : IsKappaSmall κ B) (hL : IsKappaSmall κ L)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ leftKanShape (indYoneda κ C) x)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ leftKanShape (indYoneda κ C) x)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (h : (SSet.uliftFunctor.{u + 1, u}).map i ≫ H = t ≫ sliceUnderProjection z) :
    ∃ (c : JoinCocone H) (d : JoinCocone t),
      d.val ≫ sliceUnderProjection z =
        joinMap ((SSet.uliftFunctor.{u + 1, u}).map i) (𝟙 (Δ[0] : SSet.{u + 1})) ≫ c.val := by
  let g := joinInr L A
  let e := uliftJoinIso.{u, u + 1} L A
  let hp := uliftSSet_isPushout.{u, u + 1} (IsPushout.of_hasPushout i g)
  have ht : (SSet.uliftFunctor.{u + 1, u}).map i ≫ H =
      (SSet.uliftFunctor.{u + 1, u}).map g ≫ e.hom ≫ sliceUnderUncurry t := by
    rw [← Category.assoc, uliftJoinIso_inr, sliceUnderUncurry_projection]
    exact h
  let F := hp.desc H (e.hom ≫ sliceUnderUncurry t) ht
  let jB := (SSet.uliftFunctor.{u + 1, u}).map (pushout.inl i g)
  let jT := e.inv ≫ (SSet.uliftFunctor.{u + 1, u}).map (pushout.inr i g)
  have hj : (SSet.uliftFunctor.{u + 1, u}).map i ≫ jB =
      joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L)
        ((SSet.uliftFunctor.{u + 1, u}).obj A) ≫ jT := by
    dsimp only [jB, jT]
    rw [← uliftJoinIso_inr L A, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, ← Functor.map_comp, pushout.condition]
  have hFB : jB ≫ F = H := hp.inl_desc _ _ _
  have hFT : jT ≫ F = sliceUnderUncurry t := by
    dsimp only [jT]
    rw [Category.assoc, hp.inr_desc, Iso.inv_hom_id_assoc]
  have hP := isKappaSmall_pushout_of_mono (Fact.out : κ.IsRegular) i g hB
    (isKappaSmall_join (Fact.out : κ.IsRegular) hL hA)
  obtain ⟨c₀⟩ := nonempty_indComma_cocone κ x hP F
  exact relativeCocones_of_commonCocone _ H z t jB jT hj F hFB hFT c₀
end SerrePositivity.InfinityCategories.F2.Ind
