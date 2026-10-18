module

public import SerrePositivity.InfinityCategories.F1.CocartesianCoslice

/-!
概要：相対 coslice の trivial Kan fibration 性から cocartesian 性を導く。
方針：外側ホーンの図式を join 上の二つの錐に戻して境界を持ち上げる。
規約：始点は一次の左ホーンで表す。
使われ方：Kerodon Proposition 5.1.1.14 の cocartesian 側の逆方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 coslice 制限が trivial Kan fibration なら指定辺は cocartesian。
方針：指定辺を持つ外側ホーンを二つの錐に分解し、相対 coslice の境界を充填する。
規約：quasicategory 性や inner fibration 性の追加仮定は不要。
使われ方：Kerodon Proposition 5.1.1.14、cocartesian 性の coslice による検出。 -/
lemma isCocartesianEdge_of_relativeCosliceMap_trivialKanFibration {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y)
    (hq : TrivialKanFibration (relativeCosliceMap e q (horn 1 0))) :
    IsCocartesianEdge q (SSet.yonedaEquiv e) := by
  intro n σ β he sq
  let K := (Δ[1] : SSet.{u})
  let A := (Δ[n] : SSet.{u})
  let K₀ := horn.{u} 1 0
  let A₀ := boundary.{u} n
  let hs := joinUnion_isPushout K₀ A₀
  let T := (initialHornJoinIso n).hom ≫ σ
  let D := (initialEdgeJoinIso n).hom ≫ β
  let G := joinUnionRight K₀ A₀ ≫ T
  let H := joinUnionLeft K₀ A₀ ≫ T
  have hTD : T ≫ q = (joinUnion K₀ A₀).ι ≫ D := by
    dsimp only [T, D]
    rw [Category.assoc, sq.w, ← Category.assoc, initialHornJoinIso_hom_ι, Category.assoc]
  have hover : joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H =
      joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G := by
    simpa only [H, G, Category.assoc] using congrArg (fun f ↦ f ≫ T) hs.w
  have hG : joinInl K (A₀ : SSet.{u}) ≫ G = e := by
    apply SSet.yonedaEquiv.injective
    change SSet.yonedaEquiv ((joinInl K (A₀ : SSet.{u}) ≫ joinUnionRight K₀ A₀ ≫
      (initialHornJoinIso n).hom) ≫ σ) = _
    rw [SSet.yonedaEquiv_comp, initialHornJoinIso_edge]
    exact he
  have hH : joinInl (K₀ : SSet.{u}) A ≫ H = K₀.ι ≫ e := by
    have h := congrArg (fun f ↦ joinInl (K₀ : SSet.{u}) (A₀ : SSet.{u}) ≫ f) hover
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    rw [← Category.assoc (joinInl (K₀ : SSet.{u}) (A₀ : SSet.{u}))
      (joinMap K₀.ι (𝟙 (A₀ : SSet.{u}))) G, joinInl_joinMap, Category.assoc, hG] at h
    exact h
  have hGq : G ≫ q = joinMap (𝟙 K) A₀.ι ≫ D := by
    dsimp only [G]
    rw [Category.assoc, hTD, ← Category.assoc, joinUnionRight_ι]
  have hHq : H ≫ q = joinMap K₀.ι (𝟙 A) ≫ D := by
    dsimp only [H]
    rw [Category.assoc, hTD, ← Category.assoc, joinUnionLeft_ι]
  have hD : joinInl K A ≫ D = e ≫ q := by
    have h := congrArg (fun f ↦ joinInl K (A₀ : SSet.{u}) ≫ f) hGq
    rw [← Category.assoc, hG, ← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.symm
  let a := sliceUnderCurry G hG
  let b₁ := sliceUnderCurry H hH
  let b₂ := sliceUnderCurry D hD
  have hw : b₁ ≫ sliceUnderPostcomp (K₀.ι ≫ e) q =
      b₂ ≫ sliceUnderRestrict (e ≫ q) K₀.ι := by
    apply sliceUnderUncurry_injective ((K₀.ι ≫ e) ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact hHq
  let b := pullback.lift b₁ b₂ hw
  let r := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ e) q)
    (sliceUnderRestrict (e ≫ q) K₀.ι)
  let s := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ e) q)
    (sliceUnderRestrict (e ≫ q) K₀.ι)
  have has : a ≫ relativeCosliceMap e q K₀ = A₀.ι ≫ b := by
    apply pullback.hom_ext
    · change a ≫ relativeCosliceMap e q K₀ ≫ r = (A₀.ι ≫ b) ≫ r
      have hr : relativeCosliceMap e q K₀ ≫ r = sliceUnderRestrict e K₀.ι :=
        pullback.lift_fst _ _ _
      rw [hr, Category.assoc, pullback.lift_fst]
      apply sliceUnderUncurry_injective (K₀.ι ≫ e)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp,
        sliceUnderUncurry_curry, sliceUnderUncurry_curry]
      exact hover.symm
    · change a ≫ relativeCosliceMap e q K₀ ≫ s = (A₀.ι ≫ b) ≫ s
      have hr : relativeCosliceMap e q K₀ ≫ s = sliceUnderPostcomp e q :=
        pullback.lift_snd _ _ _
      rw [hr, Category.assoc, pullback.lift_snd]
      apply sliceUnderUncurry_injective (e ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp,
        sliceUnderUncurry_curry, sliceUnderUncurry_curry]
      exact hGq
  have := hq.mem (boundary n).ι inferInstance
  let sq₀ : CommSq a A₀.ι (relativeCosliceMap e q K₀) b := ⟨has⟩
  let L := sliceUnderUncurry sq₀.lift
  have hLG : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    have h := congrArg sliceUnderUncurry sq₀.fac_left
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry] at h
    exact h
  have hLH : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    have h := congrArg (fun f ↦ f ≫ r) sq₀.fac_right
    change sq₀.lift ≫ relativeCosliceMap e q K₀ ≫ r = b ≫ r at h
    rw [show relativeCosliceMap e q K₀ ≫ r = sliceUnderRestrict e K₀.ι from
      pullback.lift_fst _ _ _, pullback.lift_fst] at h
    have hh := congrArg sliceUnderUncurry h
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry] at hh
    exact hh
  have hLq : L ≫ q = D := by
    have h := congrArg (fun f ↦ f ≫ s) sq₀.fac_right
    change sq₀.lift ≫ relativeCosliceMap e q K₀ ≫ s = b ≫ s at h
    rw [show relativeCosliceMap e q K₀ ≫ s = sliceUnderPostcomp e q from
      pullback.lift_snd _ _ _, pullback.lift_snd] at h
    have hh := congrArg sliceUnderUncurry h
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry] at hh
    exact hh
  have hLT : (joinUnion K₀ A₀).ι ≫ L = T := by
    apply hs.hom_ext
    · rw [← Category.assoc, joinUnionLeft_ι, hLH]
    · rw [← Category.assoc, joinUnionRight_ι, hLG]
  refine CommSq.HasLift.mk' {
    l := (initialEdgeJoinIso n).inv ≫ L
    fac_left := ?_
    fac_right := ?_ }
  · apply (cancel_epi (initialHornJoinIso n).hom).1
    rw [← Category.assoc, initialHornJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id_assoc, hLT]
  · rw [Category.assoc, hLq]
    exact (initialEdgeJoinIso n).inv_hom_id_assoc β

/-- 概要：cocartesian 性と相対 coslice 制限の trivial Kan fibration 性は同値。
方針：初期ホーンと coslice の境界充填の間の往復を組み合わせる。
規約：始点の部分図式を Λ[1,0] で表す。
使われ方：Kerodon Proposition 5.1.1.14、cocartesian 辺の普遍性による特徴づけ。 -/
lemma isCocartesianEdge_iff_relativeCosliceMap_trivialKanFibration {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y) :
    IsCocartesianEdge q (SSet.yonedaEquiv e) ↔
      TrivialKanFibration (relativeCosliceMap e q (horn 1 0)) :=
  ⟨relativeCosliceMap_trivialKanFibration_of_isCocartesianEdge e q,
    isCocartesianEdge_of_relativeCosliceMap_trivialKanFibration e q⟩

end SerrePositivity.InfinityCategories
