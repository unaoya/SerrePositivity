module

public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：inner fibration に対する相対 coslice の射は left fibration。
方針：持ち上げ問題を空の左因子を使う pushout-join の相対充填へ移す。
規約：元と標的の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.3.6.9、§5.1.1 の輸送の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：coslice の後合成と射影を相対的な引き戻しの射に合わせる。
方針：二つの射影の可換性から pullback へ持ち上げる。
規約：左に固定する図式 a は任意。
使われ方：Kerodon Corollary 4.3.6.9 の相対 coslice の射。 -/
noncomputable def cosliceEndpointMap {K E B : SSet.{u}} (a : K ⟶ E) (p : E ⟶ B) :
    sliceUnder a ⟶ pullback p (sliceUnderProjection (a ≫ p)) :=
  pullback.lift (sliceUnderProjection a) (sliceUnderPostcomp a p) rfl

/-- 概要：相対 coslice の第一射影は元の coslice 射影。
方針：pullback の持ち上げの計算。
規約：図式は任意。
使われ方：Kerodon §5.1.1 の相対的な射影。 -/
lemma cosliceEndpointMap_fst {K E B : SSet.{u}} (a : K ⟶ E) (p : E ⟶ B) :
    cosliceEndpointMap a p ≫ pullback.fst p (sliceUnderProjection (a ≫ p)) = sliceUnderProjection a :=
  pullback.lift_fst _ _ _

/-- 概要：相対 coslice の第二射影は coslice の後合成。
方針：pullback の持ち上げの計算。
規約：図式は任意。
使われ方：Kerodon §5.1.1 の相対的な図式の像。 -/
lemma cosliceEndpointMap_snd {K E B : SSet.{u}} (a : K ⟶ E) (p : E ⟶ B) :
    cosliceEndpointMap a p ≫ pullback.snd p (sliceUnderProjection (a ≫ p)) = sliceUnderPostcomp a p :=
  pullback.lift_snd _ _ _

/-- 概要：相対 coslice の射は left anodyne な部分複体包含を持ち上げる。
方針：境界の錐と新しい頂点の射を pushout-join 上で貼り、元の inner fibration で充填する。
規約：a は任意、p の inner fibration 性だけを使う。
使われ方：Kerodon Corollary 4.3.6.9 の相対充填。 -/
lemma cosliceEndpointMap_hasLiftingProperty {A K E B : SSet.{u}}
    (a : K ⟶ E) (p : E ⟶ B) [InnerFibration p]
    (A₀ : A.Subcomplex) (hA : leftAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (cosliceEndpointMap a p) := by
  constructor
  intro u b sq
  let Z : SSet.{u} := (⊥ : K.Subcomplex)
  let G := sliceUnderUncurry u
  let H := (emptyJoinIso K A).hom ≫ b ≫ pullback.fst p (sliceUnderProjection (a ≫ p))
  let F := sliceUnderUncurry (b ≫ pullback.snd p (sliceUnderProjection (a ≫ p)))
  have hfirst : u ≫ sliceUnderProjection a =
      A₀.ι ≫ b ≫ pullback.fst p (sliceUnderProjection (a ≫ p)) := by
    have hh := congrArg (fun t ↦ t ≫ pullback.fst p (sliceUnderProjection (a ≫ p))) sq.w
    simpa only [Category.assoc, cosliceEndpointMap_fst] using hh
  have hsecond : G ≫ p = joinMap (𝟙 K) A₀.ι ≫ F := by
    have hh := congrArg (fun t ↦ t ≫ pullback.snd p (sliceUnderProjection (a ≫ p))) sq.w
    simp only [Category.assoc, cosliceEndpointMap_snd] at hh
    have hu := congrArg sliceUnderUncurry hh
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hu
    exact hu
  have hover : joinMap (⊥ : K.Subcomplex).ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 Z) A₀.ι ≫ H := by
    apply (cancel_epi (emptyJoinIso K (A₀ : SSet.{u})).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp,
      ← Category.assoc, joinInr_joinMap, Category.assoc]
    change joinInr K (A₀ : SSet.{u}) ≫ G =
      A₀.ι ≫ ((emptyJoinIso K A).inv ≫ ((emptyJoinIso K A).hom ≫
        b ≫ pullback.fst p (sliceUnderProjection (a ≫ p))))
    rw [Iso.inv_hom_id_assoc, sliceUnderUncurry_projection]
    exact hfirst
  let hs := (joinUnion_isPushout (⊥ : K.Subcomplex) A₀).flip
  let T := hs.desc G H hover
  have hH : H ≫ p = joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ F := by
    apply (cancel_epi (emptyJoinIso K A).inv).1
    simp only [H, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (emptyJoinIso K A).inv, emptyJoinIso_inv, joinInr_joinMap,
      Category.id_comp, pullback.condition]
    simpa only [Category.assoc] using (sliceUnderUncurry_projection
      (b ≫ pullback.snd p (sliceUnderProjection (a ≫ p)))).symm

  have hT : CommSq T (joinUnion (⊥ : K.Subcomplex) A₀).ι p F := by
    constructor
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, reassoc_of% joinUnionRight_ι]
      exact hsecond
    · rw [← Category.assoc, hs.inr_desc, reassoc_of% joinUnionLeft_ι]
      exact hH
  have := joinUnion_innerAnodyne_of_leftAnodyne (⊥ : K.Subcomplex) A₀ hA p InnerFibration.mem
  let L := hT.lift
  have hleft : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc, hT.fac_left]
    exact hs.inl_desc _ _ _
  have hright : joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc, hT.fac_left]
    exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = a := by
    have hh := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hleft
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed u)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hleft
  · apply pullback.hom_ext
    · rw [Category.assoc, cosliceEndpointMap_fst, sliceUnderCurry_projection]
      have hh := congrArg (fun z ↦ (emptyJoinIso K A).inv ≫ z) hright
      rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp] at hh
      exact hh.trans (by dsimp [H]; rw [← emptyJoinIso_inv, Iso.inv_hom_id_assoc])
    · rw [Category.assoc, cosliceEndpointMap_snd]
      apply sliceUnderUncurry_injective (a ≫ p)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hT.fac_right

/-- 概要：inner fibration の相対 coslice の射は left fibration。
方針：左ホーン包含に対する相対持ち上げ補題を適用する。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.3.6.9、§5.1.1 の相対 coslice。 -/
instance cosliceEndpointMap_leftFibration {K E B : SSet.{u}}
    (a : K ⟶ E) (p : E ⟶ B) [InnerFibration p] : LeftFibration (cosliceEndpointMap a p) where
  mem := by
    intro A B f hf
    cases hf with
    | intro i hi => exact cosliceEndpointMap_hasLiftingProperty a p _ (leftAnodyneExtensions_horn i hi)

end SerrePositivity.InfinityCategories
