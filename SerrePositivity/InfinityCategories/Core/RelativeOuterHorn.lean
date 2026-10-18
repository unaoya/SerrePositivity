module

public import SerrePositivity.InfinityCategories.Core.RelativeCoslice
public import SerrePositivity.InfinityCategories.Core.InvertibleEdge

/-!
概要：可逆な右辺を持つ pushout-join の相対的な充填。
方針：相対 coslice の左ファイブレーションに可逆な辺を持ち上げる。
規約：標的の全 join の図式を厳密に保つ。
使われ方：HTT Proposition 1.2.4.3、Kerodon §4.4.2 の相対版。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：inner fibration に沿って、可逆な右辺を持つ pushout-join の図式を持ち上げる。
方針：相対 coslice の左ファイブレーションと、可逆辺の終点での持ち上げを使う。
規約：元の joinUnion の図式と標的の全 join の図式をともに固定する。
使われ方：HTT Proposition 1.2.4.3、Kerodon §4.4.2 の相対外側ホーン。 -/
lemma joinUnion_lift_of_invertible_rightEdge {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (q : X ⟶ Y) [InnerFibration q]
    (K₀ : K.Subcomplex) (T : (joinUnion K₀ (horn 1 1) : SSet.{u}) ⟶ X)
    (W : join K (Δ[1] : SSet.{u}) ⟶ Y)
    (hTW : T ≫ q = (joinUnion K₀ (horn 1 1)).ι ≫ W)
    (he : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (joinInr (K₀ : SSet.{u}) Δ[1] ≫
        joinUnionLeft K₀ (horn 1 1) ≫ T)))) :
    ∃ L : join K (Δ[1] : SSet.{u}) ⟶ X, (joinUnion K₀ (horn 1 1)).ι ≫ L = T ∧ L ≫ q = W := by
  let B₀ : (Δ[1] : SSet.{u}).Subcomplex := horn 1 1
  let hs := joinUnion_isPushout K₀ B₀
  let G := joinUnionLeft K₀ B₀ ≫ T
  let H := joinUnionRight K₀ B₀ ≫ T
  have hover : joinMap (𝟙 (K₀ : SSet.{u})) B₀.ι ≫ G =
      joinMap K₀.ι (𝟙 (B₀ : SSet.{u})) ≫ H := by
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ T) hs.w
  let p := joinInl K (B₀ : SSet.{u}) ≫ H
  have hG : joinInl (K₀ : SSet.{u}) Δ[1] ≫ G = K₀.ι ≫ p := by
    have h := congrArg (fun z ↦ joinInl (K₀ : SSet.{u}) (B₀ : SSet.{u}) ≫ z) hover
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    rw [← Category.assoc (joinInl (K₀ : SSet.{u}) (B₀ : SSet.{u}))
      (joinMap K₀.ι (𝟙 (B₀ : SSet.{u}))) H, joinInl_joinMap, Category.assoc] at h
    exact h
  let a := sliceUnderCurry G hG
  let b := sliceUnderCurry H (show joinInl K (B₀ : SSet.{u}) ≫ H = p from rfl)
  let r₀ := sliceUnderRestrict p K₀.ι
  have sq : CommSq b B₀.ι r₀ a := by
    constructor
    apply sliceUnderUncurry_injective (K₀.ι ≫ p)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact hover.symm
  have hGq : G ≫ q = joinMap K₀.ι (𝟙 Δ[1]) ≫ W := by
    have h := congrArg (fun z ↦ joinUnionLeft K₀ B₀ ≫ z) hTW
    change G ≫ q = (joinUnionLeft K₀ B₀ ≫ (joinUnion K₀ B₀).ι) ≫ W at h
    rw [joinUnionLeft_ι] at h
    exact h
  have hHq : H ≫ q = joinMap (𝟙 K) B₀.ι ≫ W := by
    have h := congrArg (fun z ↦ joinUnionRight K₀ B₀ ≫ z) hTW
    change H ≫ q = (joinUnionRight K₀ B₀ ≫ (joinUnion K₀ B₀).ι) ≫ W at h
    rw [joinUnionRight_ι] at h
    exact h
  have hW : joinInl K Δ[1] ≫ W = p ≫ q := by
    have h := congrArg (fun z ↦ joinInl K (B₀ : SSet.{u}) ≫ z) hHq
    change (joinInl K (B₀ : SSet.{u}) ≫ H) ≫ q =
      (joinInl K (B₀ : SSet.{u}) ≫ joinMap (𝟙 K) B₀.ι) ≫ W at h
    rw [joinInl_joinMap, Category.id_comp] at h
    exact h.symm
  let c := sliceUnderCurry W hW
  have hac : a ≫ sliceUnderPostcomp (K₀.ι ≫ p) q = c ≫ sliceUnderRestrict (p ≫ q) K₀.ι := by
    apply sliceUnderUncurry_injective ((K₀.ι ≫ p) ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact hGq
  let r : relativeCosliceTarget p q K₀ ⟶ sliceUnder (K₀.ι ≫ p) := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let s : relativeCosliceTarget p q K₀ ⟶ sliceUnder (p ≫ q) := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let d : (Δ[1] : SSet.{u}) ⟶ relativeCosliceTarget p q K₀ := pullback.lift a c hac
  have hd₁ : d ≫ r = a := pullback.lift_fst _ _ _
  have hd₂ : d ≫ s = c := pullback.lift_snd _ _ _
  have hbc : b ≫ sliceUnderPostcomp p q = B₀.ι ≫ c := by
    apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp,
      sliceUnderUncurry_curry, sliceUnderUncurry_curry]
    exact hHq
  have hsqd : CommSq b B₀.ι (relativeCosliceMap p q K₀) d := by
    constructor
    apply pullback.hom_ext
    · have hr : relativeCosliceMap p q K₀ ≫ r = sliceUnderRestrict p K₀.ι :=
        pullback.lift_fst _ _ _
      change b ≫ relativeCosliceMap p q K₀ ≫ r = B₀.ι ≫ d ≫ r
      rw [hr, hd₁]
      exact sq.w
    · have hs : relativeCosliceMap p q K₀ ≫ s = sliceUnderPostcomp p q :=
        pullback.lift_snd _ _ _
      change b ≫ relativeCosliceMap p q K₀ ≫ s = B₀.ι ≫ d ≫ s
      rw [hs, hd₂]
      exact hbc
  have hmap : IsInvertibleEdge ((edgeOfSimplex (SSet.yonedaEquiv a)).map
      ((truncation 2).map (sliceUnderProjection (K₀.ι ≫ p)))) := by
    have hc : ((edgeOfSimplex (SSet.yonedaEquiv a)).map
        ((truncation 2).map (sliceUnderProjection (K₀.ι ≫ p)))).edge =
        (edgeOfSimplex (SSet.yonedaEquiv (joinInr (K₀ : SSet.{u}) Δ[1] ≫ G))).edge := by
      change (sliceUnderProjection (K₀.ι ≫ p)).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv a) = _
      rw [← SSet.yonedaEquiv_comp]
      exact congrArg SSet.yonedaEquiv (sliceUnderCurry_projection G hG)
    exact (isInvertibleEdge_congr hc).2 he
  have ha : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv a)) :=
    leftFibration_reflects_invertibleEdge (sliceUnderProjection (K₀.ι ≫ p)) _ hmap
  have hdmap : IsInvertibleEdge (X := sliceUnder (K₀.ι ≫ p)) ((edgeOfSimplex (SSet.yonedaEquiv d)).map
      ((truncation 2).map r)) := by
    have h : ((edgeOfSimplex (SSet.yonedaEquiv d)).map ((truncation 2).map r)).edge =
        (edgeOfSimplex (SSet.yonedaEquiv a)).edge := by
      change r.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv d) = _
      rw [← SSet.yonedaEquiv_comp, hd₁]
      rfl
    exact (isInvertibleEdge_congr h).mpr ha
  have hd : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv d)) :=
    leftFibration_reflects_invertibleEdge r _ hdmap
  obtain ⟨F, hF₁, hFd⟩ := leftFibration_liftHorn_one_last (relativeCosliceMap p q K₀) b d hsqd hd
  have hFa : F ≫ sliceUnderRestrict p K₀.ι = a := by
    have h := congrArg (fun z ↦ z ≫ r) hFd
    have hr : relativeCosliceMap p q K₀ ≫ r = sliceUnderRestrict p K₀.ι :=
      pullback.lift_fst _ _ _
    simpa only [Category.assoc, hr, hd₁] using h
  have hFc : F ≫ sliceUnderPostcomp p q = c := by
    have h := congrArg (fun z ↦ z ≫ s) hFd
    have hs : relativeCosliceMap p q K₀ ≫ s = sliceUnderPostcomp p q :=
      pullback.lift_snd _ _ _
    simpa only [Category.assoc, hs, hd₂] using h
  refine ⟨sliceUnderUncurry F, ?_, ?_⟩
  · apply hs.hom_ext
    · change joinUnionLeft K₀ B₀ ≫ ((joinUnion K₀ B₀).ι ≫ sliceUnderUncurry F) = G
      rw [← Category.assoc, joinUnionLeft_ι]
      have h := congrArg sliceUnderUncurry hFa
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry] at h
      exact h
    · change joinUnionRight K₀ B₀ ≫ ((joinUnion K₀ B₀).ι ≫ sliceUnderUncurry F) = H
      rw [← Category.assoc, joinUnionRight_ι]
      have h := congrArg sliceUnderUncurry hF₁
      rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry] at h
      exact h
  · have h := congrArg sliceUnderUncurry hFc
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry] at h
    exact h

/-- 概要：inner fibration は可逆な最後の辺を持つ外側ホーンを持ち上げる。
方針：最後のホーンを境界と区間の pushout-join に同定し、相対 coslice で充填する。
規約：指定された標的の単体を厳密に持ち上げる。
使われ方：HTT Proposition 1.2.4.3、Kerodon §4.4.2 の相対版。 -/
lemma innerFibration_lift_finalHorn {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (q : X ⟶ Y) [InnerFibration q] (n : ℕ)
    (σ : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X)
    (β : (Δ[n + 2] : SSet.{u}) ⟶ Y)
    (hσq : σ ≫ q = (horn (n + 2) (Fin.last (n + 2))).ι ≫ β)
    (he : IsInvertibleEdge (edgeOfSimplex
      (σ.app (Opposite.op ⦋1⦌) (finalHornEdge n)))) :
    ∃ F : (Δ[n + 2] : SSet.{u}) ⟶ X,
      (horn (n + 2) (Fin.last (n + 2))).ι ≫ F = σ ∧ F ≫ q = β := by
  let T := (finalHornJoinIso n).hom ≫ σ
  let W := (joinStdSimplexIso n 1).hom ≫ β
  have hTW : T ≫ q = (joinUnion (boundary n) (horn 1 1)).ι ≫ W := by
    rw [Category.assoc, hσq, ← Category.assoc, finalHornJoinIso_hom_ι, Category.assoc]
  let R := joinInr (boundary n : SSet.{u}) Δ[1] ≫
    joinUnionLeft (boundary n) (horn 1 1) ≫ (finalHornJoinIso n).hom
  have hR : R ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      joinInr (Δ[n] : SSet.{u}) Δ[1] ≫ (joinStdSimplexIso n 1).hom := by
    dsimp only [R]
    simp only [Category.assoc]
    rw [finalHornJoinIso_hom_ι,
      ← Category.assoc (joinUnionLeft (boundary n) (horn 1 1))
        (joinUnion (boundary n) (horn 1 1)).ι (joinStdSimplexIso n 1).hom,
      joinUnionLeft_ι, ← Category.assoc, joinInr_joinMap, Category.id_comp]
  have hr : SSet.yonedaEquiv R = finalHornEdge n := by
    apply Subtype.ext
    change (horn (n + 2) (Fin.last (n + 2))).ι.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv R) = _
    rw [← SSet.yonedaEquiv_comp, hR]
    exact joinStdSimplexIso_inr_edge n
  have hEdge : IsInvertibleEdge (edgeOfSimplex
      (SSet.yonedaEquiv (joinInr (boundary n : SSet.{u}) Δ[1] ≫
        joinUnionLeft (boundary n) (horn 1 1) ≫ T))) := by
    have hc : SSet.yonedaEquiv (joinInr (boundary n : SSet.{u}) Δ[1] ≫
        joinUnionLeft (boundary n) (horn 1 1) ≫ T) =
        σ.app (Opposite.op ⦋1⦌) (finalHornEdge n) := by
      change SSet.yonedaEquiv (R ≫ σ) = _
      rw [SSet.yonedaEquiv_comp, hr]
    exact (isInvertibleEdge_congr hc).mpr he
  obtain ⟨L, hL, hLq⟩ := joinUnion_lift_of_invertible_rightEdge q (boundary n) T W hTW hEdge
  refine ⟨(joinStdSimplexIso n 1).inv ≫ L, ?_, ?_⟩
  · apply (cancel_epi (finalHornJoinIso n).hom).1
    rw [← Category.assoc, finalHornJoinIso_hom_ι, Category.assoc, Iso.hom_inv_id_assoc]
    exact hL
  · rw [Category.assoc, hLq]
    exact (joinStdSimplexIso n 1).inv_hom_id_assoc β

end SerrePositivity.InfinityCategories
