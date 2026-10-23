module

public import SerrePositivity.InfinityCategories.F1.Simplicial.InitialHornJoin
public import SerrePositivity.InfinityCategories.Core.RelativeCoslice

/-!
概要：cocartesian 辺から相対 coslice の trivial Kan fibration 性を導く。
方針：coslice の境界持ち上げを指定辺を持つ最初の外側ホーンの充填へ移す。
規約：射 q に inner fibration 性を追加で仮定しない。
使われ方：Kerodon Proposition 5.1.1.14、cocartesian 辺の合成則の準備。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian 辺の相対 coslice 制限は全ての境界を持ち上げる。
方針：二つの錐を pushout-join 上で貼り、初期ホーンの同型で cocartesian 性を適用する。
規約：零次の境界も含む。
使われ方：Kerodon Proposition 5.1.1.14 の cocartesian 側の順方向。 -/
lemma relativeCosliceMap_boundary_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : IsCocartesianEdge q (SSet.yonedaEquiv e)) (n : ℕ) :
    HasLiftingProperty (boundary n).ι (relativeCosliceMap e q (horn 1 0)) := by
  let K := (Δ[1] : SSet.{u})
  let A := (Δ[n] : SSet.{u})
  let K₀ := horn.{u} 1 0
  let A₀ := boundary.{u} n
  constructor
  intro a b sq
  let r := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ e) q)
    (sliceUnderRestrict (e ≫ q) K₀.ι)
  let s := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ e) q)
    (sliceUnderRestrict (e ≫ q) K₀.ι)
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry (b ≫ r)
  let B := sliceUnderUncurry (b ≫ s)
  have ha : a ≫ sliceUnderRestrict e K₀.ι = A₀.ι ≫ (b ≫ r) := by
    have h := congrArg (fun f ↦ f ≫ r) sq.w
    simpa only [r, K₀, A₀, relativeCosliceMap, Category.assoc, pullback.lift_fst] using h
  have hb : a ≫ sliceUnderPostcomp e q = A₀.ι ≫ (b ≫ s) := by
    have h := congrArg (fun f ↦ f ≫ s) sq.w
    simpa only [s, K₀, A₀, relativeCosliceMap, Category.assoc, pullback.lift_snd] using h
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
      have h : (b ≫ r) ≫ sliceUnderPostcomp (K₀.ι ≫ e) q =
          (b ≫ s) ≫ sliceUnderRestrict (e ≫ q) K₀.ι := by
        simpa only [r, s, Category.assoc] using congrArg (fun z ↦ b ≫ z)
          (pullback.condition (f := sliceUnderPostcomp (K₀.ι ≫ e) q)
            (g := sliceUnderRestrict (e ≫ q) K₀.ι))
      have hh := congrArg sliceUnderUncurry h
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict] at hh
      exact hh
    · rw [← Category.assoc, hs.inr_desc, ← Category.assoc, joinUnionRight_ι]
      have h := congrArg sliceUnderUncurry hb
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
      exact h
  let σ := (initialHornJoinIso n).inv ≫ T
  let β := (initialEdgeJoinIso n).inv ≫ B
  have hσq : σ ≫ q = (horn (n + 2) 0).ι ≫ β := by
    dsimp only [σ, β]
    rw [Category.assoc, hTB, ← Category.assoc, initialHornJoinIso_inv_ι, Category.assoc]
  let R := joinInl K (A₀ : SSet.{u}) ≫ joinUnionRight K₀ A₀
  have hRT : R ≫ T = e := by
    dsimp only [R, T]
    rw [Category.assoc, hs.inr_desc]
    exact sliceUnderUncurry_fixed a
  have hσ : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = SSet.yonedaEquiv e := by
    have hh : (R ≫ (initialHornJoinIso n).hom) ≫ σ = R ≫ T := by
      dsimp only [σ]
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    have h := congrArg SSet.yonedaEquiv hh
    rw [SSet.yonedaEquiv_comp] at h
    have hR : SSet.yonedaEquiv (R ≫ (initialHornJoinIso n).hom) = initialHornEdge n :=
      initialHornJoinIso_edge n
    rw [hR, hRT] at h
    exact h
  let sq₀ : CommSq σ (horn (n + 2) 0).ι q β := ⟨hσq⟩
  have := he n σ β hσ sq₀
  let L := (initialEdgeJoinIso n).hom ≫ sq₀.lift
  have hTL : (joinUnion K₀ A₀).ι ≫ L = T := by
    dsimp only [L]
    rw [← Category.assoc, ← initialHornJoinIso_hom_ι, Category.assoc, sq₀.fac_left]
    dsimp only [σ]
    rw [Iso.hom_inv_id_assoc]
  have hLq : L ≫ q = B := by
    dsimp only [L]
    rw [Category.assoc, sq₀.fac_right]
    exact (initialEdgeJoinIso n).hom_inv_id_assoc B
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ L) = H
    rw [hTL]
    exact hs.inl_desc _ _ _
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ L) = G
    rw [hTL]
    exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = e := by
    have h := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective e
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap e q K₀ ≫ r = b ≫ r
      have hr : relativeCosliceMap e q K₀ ≫ r = sliceUnderRestrict e K₀.ι :=
        pullback.lift_fst _ _ _
      rw [hr]
      apply sliceUnderUncurry_injective (K₀.ι ≫ e)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hleft
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap e q K₀ ≫ s = b ≫ s
      have hs : relativeCosliceMap e q K₀ ≫ s = sliceUnderPostcomp e q :=
        pullback.lift_snd _ _ _
      rw [hs]
      apply sliceUnderUncurry_injective (e ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hLq

/-- 概要：cocartesian 辺の相対 coslice 制限は trivial Kan fibration。
方針：全次元の境界持ち上げ性による判定を使う。
規約：射 q に inner fibration 性を仮定しない。
使われ方：Kerodon Proposition 5.1.1.14 の cocartesian 側の順方向。 -/
lemma relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (he : IsCocartesianEdge q (SSet.yonedaEquiv e)) :
    TrivialKanFibration (relativeCosliceMap e q (horn 1 0)) :=
  (trivialKanFibration_iff_boundary _).2
    (relativeCosliceMap_boundary_of_isCocartesianEdge e q he)

end SerrePositivity.InfinityCategories
