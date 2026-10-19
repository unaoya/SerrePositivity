module
public import SerrePositivity.InfinityCategories.Core.RelativeCoslice
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialBoundary

/-! # 相対始対象の点の coslice の普遍性
概要：相対始点境界充填条件から、点の coslice の相対比較は trivial Kan fibration となる。
方針：coslice の境界と標的の単体を join の境界へ貼り、指定された基底上で充填する。
規約：ファイブレーション性を追加仮定しない。使われ方：HTT §1.2.12・§2.1.2、余極限の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial

/-- 概要：相対始対象の点の coslice の比較は全境界を持ち上げる。
方針：点と境界を貼った標準境界に相対始点境界充填を適用する。
規約：X・Y の quasicategory 性も q の inner fibration 性も要求しない。
使われ方：異なる図式の間の余極限余錐の輸送。 -/
lemma relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting {X Y : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (hx : InitialBoundaryLifting q (SSet.yonedaEquiv p)) :
    TrivialKanFibration (relativeCosliceMap p q (boundary 0)) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  let K : SSet.{u} := Δ[0]
  let A : SSet.{u} := Δ[n]
  let K₀ : K.Subcomplex := boundary 0
  let A₀ : A.Subcomplex := boundary n
  change HasLiftingProperty A₀.ι (relativeCosliceMap p q K₀)
  constructor
  intro a b sq
  let r := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let s := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry (b ≫ r)
  let B := sliceUnderUncurry (b ≫ s)
  have ha : a ≫ sliceUnderRestrict p K₀.ι = A₀.ι ≫ (b ≫ r) := by
    have h := congrArg (fun f ↦ f ≫ r) sq.w
    simpa only [r, relativeCosliceMap, Category.assoc, pullback.lift_fst] using h
  have hb : a ≫ sliceUnderPostcomp p q = A₀.ι ≫ (b ≫ s) := by
    have h := congrArg (fun f ↦ f ≫ s) sq.w
    simpa only [s, relativeCosliceMap, Category.assoc, pullback.lift_snd] using h
  have hover : joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H := by
    have h := congrArg sliceUnderUncurry ha
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at h
    exact h
  let hs := joinUnion_isPushout K₀ A₀
  let T := hs.desc H G hover.symm
  have hTB : T ≫ q = (joinUnion K₀ A₀).ι ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, ← Category.assoc, joinUnionLeft_ι]
      have h : (b ≫ r) ≫ sliceUnderPostcomp (K₀.ι ≫ p) q =
          (b ≫ s) ≫ sliceUnderRestrict (p ≫ q) K₀.ι := by
        simpa only [r, s, Category.assoc] using congrArg (fun z ↦ b ≫ z)
          (pullback.condition (f := sliceUnderPostcomp (K₀.ι ≫ p) q)
            (g := sliceUnderRestrict (p ≫ q) K₀.ι))
      have hh := congrArg sliceUnderUncurry h
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict] at hh
      exact hh
    · rw [← Category.assoc, hs.inr_desc, ← Category.assoc, joinUnionRight_ι]
      have h := congrArg sliceUnderUncurry hb
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
      exact h
  let e := boundaryJoinIso.{u} 0 n
  have hfirst : boundaryVertex (0 + n) 0 ≫ (e.inv ≫ T) = p := by
    rw [← boundaryJoinIso_inl_vertex, Category.assoc, Category.assoc]
    change _ ≫ _ ≫ e.hom ≫ e.inv ≫ T = _
    rw [Iso.hom_inv_id_assoc]
    rw [hs.inr_desc]
    exact sliceUnderUncurry_fixed a
  have hi : e.inv ≫ (joinUnion K₀ A₀).ι =
      (boundary (0 + n + 1)).ι ≫ (joinStdSimplexIso 0 n).inv := by
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
      boundaryJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hsq : CommSq (e.inv ≫ T) (boundary (0 + n + 1)).ι q
      ((joinStdSimplexIso 0 n).inv ≫ B) := by
    constructor
    rw [Category.assoc, hTB, ← Category.assoc, hi, Category.assoc]
  obtain ⟨F, hF, hFq⟩ := hx (0 + n) (e.inv ≫ T) ((joinStdSimplexIso 0 n).inv ≫ B)
    (hfirst.trans (SSet.yonedaEquiv.symm_apply_apply p).symm) hsq
  let L := (joinStdSimplexIso 0 n).hom ≫ F
  have hL : (joinUnion K₀ A₀).ι ≫ L = T := by
    calc
      _ = e.hom ≫ ((boundary (0 + n + 1)).ι ≫ F) := by
        simpa only [Category.assoc] using
          (congrArg (fun z => z ≫ F) (boundaryJoinIso_hom_ι.{u} 0 n)).symm
      _ = e.hom ≫ (e.inv ≫ T) := by rw [hF]
      _ = T := Iso.hom_inv_id_assoc e T
  have hLq : L ≫ q = B := by
    dsimp only [L]
    rw [Category.assoc, hFq, Iso.hom_inv_id_assoc]
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    · rw [hL]
      exact hs.inl_desc _ _ _
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    · rw [hL]
      exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = p := by
    have h := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ r = b ≫ r
      have hr : relativeCosliceMap p q K₀ ≫ r = sliceUnderRestrict p K₀.ι :=
        pullback.lift_fst _ _ _
      rw [hr]
      apply sliceUnderUncurry_injective (K₀.ι ≫ p)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hleft
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ s = b ≫ s
      have hs : relativeCosliceMap p q K₀ ≫ s = sliceUnderPostcomp p q :=
        pullback.lift_snd _ _ _
      rw [hs]
      apply sliceUnderUncurry_injective (p ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hLq

end SerrePositivity.InfinityCategories
