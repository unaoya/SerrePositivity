module
public import SerrePositivity.InfinityCategories.Stable.ColimitCosliceRestriction
public import SerrePositivity.InfinityCategories.Core.JoinPushout
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-! # 余極限頂点の付加に沿う coslice の充填

概要：余極限余錐を図式の pushout によって付け加えると、coslice の制限は任意の単射を持ち上げる。
方針：余極限余錐の下の coslice で充填し、join が保存する pushout によって貼り合わせる。
規約：形状の射に単射性、値域に quasicategory 性を要求しない。
使われ方：S4 の左押し出しの余極限頂点を忘れる比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余極限余錐を付け加える pushout に沿う coslice 制限は任意の部分複体包含を持ち上げる。
方針：余極限 coslice の trivial Kan fibration で余錐側を充填し、残りの図式と貼り合わせる。
規約：c の図式 p と、付加後の図式 F の余錐側への制限を一致させる。
使われ方：貼り合わせにおける五頂点図式から四頂点図式への制限。 -/
lemma cosliceRestriction_lift_of_colimit_attachment {K C D X A : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (i : K ⟶ C)
    (j : join K Δ[0] ⟶ D) (k : C ⟶ D) (hp : IsPushout (joinInl K Δ[0]) i j k)
    (F : D ⟶ X) (hj : j ≫ F = c.val) (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (sliceUnderRestrict F k) := by
  constructor
  intro a b sq
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry b
  have hover : joinMap k (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 C) A₀.ι ≫ H := by
    have he := congrArg sliceUnderUncurry sq.w
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at he
    exact he
  have hi : i ≫ k ≫ F = p := by
    rw [← Category.assoc, ← hp.w, Category.assoc, hj, c.property]
  let Gc := joinMap j (𝟙 (A₀ : SSet.{u})) ≫ G
  have hGc : joinInl (join K Δ[0]) (A₀ : SSet.{u}) ≫ Gc = c.val := by
    dsimp only [Gc, G]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, sliceUnderUncurry_fixed, hj]
  let Hk := joinMap i (𝟙 A) ≫ H
  have hHk : joinInl K A ≫ Hk = p := by
    dsimp only [Hk, H]
    rw [← Category.assoc, joinInl_joinMap, Category.assoc, sliceUnderUncurry_fixed]
    exact hi
  let ac := sliceUnderCurry Gc hGc
  let bk := sliceUnderCurry Hk hHk
  have hs : CommSq ac A₀.ι (colimitCosliceRestriction c) bk := by
    constructor
    apply sliceUnderUncurry_injective p
    rw [colimitCosliceRestriction_uncurry, sliceUnderUncurry_precomp]
    dsimp only [ac, bk]
    rw [sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    have hx : joinMap (joinInl K Δ[0]) (𝟙 (A₀ : SSet.{u})) ≫ Gc =
        joinMap i (𝟙 (A₀ : SSet.{u})) ≫ (joinMap k (𝟙 (A₀ : SSet.{u})) ≫ G) := by
      dsimp only [Gc]
      simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, hp.w]
    rw [hx, hover]
    dsimp only [Hk]
    simp only [← Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id]
  have ht := colimitCosliceRestriction_trivialKanFibration c hc
  have := ht.mem A₀.ι inferInstance
  let lc := hs.lift
  let L := sliceUnderUncurry lc
  have hLk : joinMap (joinInl K Δ[0]) (𝟙 A) ≫ L = Hk := by
    have he := congrArg sliceUnderUncurry hs.fac_right
    rw [colimitCosliceRestriction_uncurry] at he
    dsimp only [bk] at he
    rw [sliceUnderUncurry_curry] at he
    exact he
  have hL₀ : joinMap (𝟙 (join K Δ[0])) A₀.ι ≫ L = Gc := by
    have he := congrArg sliceUnderUncurry hs.fac_left
    rw [sliceUnderUncurry_precomp] at he
    dsimp only [ac] at he
    rw [sliceUnderUncurry_curry] at he
    exact he
  let q := join_left_isPushout hp A
  let T := q.desc L H hLk
  have hTj : joinMap j (𝟙 A) ≫ T = L := q.inl_desc _ _ _
  have hTk : joinMap k (𝟙 A) ≫ T = H := q.inr_desc _ _ _
  have hTF : joinInl D A ≫ T = F := by
    apply hp.hom_ext
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hTj]
      dsimp only [L]
      rw [sliceUnderUncurry_fixed, hj]
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hTk]
      dsimp only [H]
      rw [sliceUnderUncurry_fixed]
  have hT₀ : joinMap (𝟙 D) A₀.ι ≫ T = G := by
    apply (join_left_isPushout hp (A₀ : SSet.{u})).hom_ext
    · have hx : joinMap j (𝟙 (A₀ : SSet.{u})) ≫ joinMap (𝟙 D) A₀.ι =
          joinMap (𝟙 (join K Δ[0])) A₀.ι ≫ joinMap j (𝟙 A) := by
        simp only [← joinMap_comp, Category.comp_id, Category.id_comp]
      rw [← Category.assoc, hx, Category.assoc, hTj, hL₀]
    · have hx : joinMap k (𝟙 (A₀ : SSet.{u})) ≫ joinMap (𝟙 D) A₀.ι =
          joinMap (𝟙 C) A₀.ι ≫ joinMap k (𝟙 A) := by
        simp only [← joinMap_comp, Category.comp_id, Category.id_comp]
      rw [← Category.assoc, hx, Category.assoc, hTk]
      exact hover.symm
  refine CommSq.HasLift.mk' { l := sliceUnderCurry T hTF, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective F
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hT₀
  · apply sliceUnderUncurry_injective (k ≫ F)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
    exact hTk

end SerrePositivity.InfinityCategories
