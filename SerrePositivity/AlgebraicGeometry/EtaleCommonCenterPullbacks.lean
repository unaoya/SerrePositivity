module

public import SerrePositivity.AlgebraicGeometry.AffineEtaleBlowupRefinement
public import SerrePositivity.AlgebraicGeometry.PureTransformOpenLocality

/-!
概要：共通の基底ブローアップへ局所中心による純変換の平坦性を移す。
方針：局所基底の主開被覆に支配射を取り、引き戻し平坦性を開被覆で貼り合わせる。
規約：局所加群はそれぞれの局所基底上で与える。
使われ方：Stacks 0814 で得た共通中心の上に、étale な始域被覆を用意する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限個の étale な局所基底で平坦化中心があれば、すべての局所純変換が平坦となる共通の基底中心を取れる。
方針：中心を因子に含む共通ブローアップを構成し、局所基底の主開被覆で支配射を使う。
規約：共通中心と各局所中心は境界元のある冪を含む。
使われ方：étale 局所の純変換の平坦性を元の加群へ降下する直前。
-/
theorem exists_common_affineBlowup_of_etale_flatPure_centers
    {R ι : Type u} [CommRing R] [IsNoetherianRing R] [Finite ι]
    (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra R (C i)]
    [∀ i, Algebra.Etale R (C i)] (J : ∀ i, Ideal (C i)) (a : R)
    (N : ι → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module (C i) (N i)]
    (hJ : ∀ i, ∃ k : ℕ, algebraMap R (C i) (a ^ k) ∈ J i)
    (hflat : ∀ i, HasFlatPurePullbacks (affineBlowupπ (J i)) (algebraMap R (C i) a) (N i)) :
    ∃ I : Ideal R, I.FG ∧ (∃ k : ℕ, a ^ k ∈ I) ∧
      ∀ i, let f := Spec.map (CommRingCat.ofHom (algebraMap R (C i)))
        HasFlatPurePullbacks (pullback.snd (affineBlowupπ I) f) (algebraMap R (C i) a) (N i) := by
  obtain ⟨I, hI, ha, h⟩ := exists_common_affineBlowup_refinement_of_etale_centers C J a hJ
  refine ⟨I, hI, ha, fun i => ?_⟩
  obtain ⟨s, hs, hdom⟩ := h i
  let b := affineBlowupπ I
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (C i)))
  let p := pullback.snd b f
  let s₀ : s → C i := fun j => j.1
  have hspan : Ideal.span (Set.range s₀) = ⊤ := by
    rw [show Set.range s₀ = (↑s : Set (C i)) from Subtype.range_val]
    exact hs
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of (C i)) s₀ hspan).openCover
  apply hasFlatPurePullbacks_of_openCover p _ _ (𝒰.pullback₁ p)
  intro j
  let g := 𝒰.f j
  let t := pullback.fst p g
  let v := pullback.snd p g
  let k := pullback.fst b f
  have hsq : (t ≫ k) ≫ b = v ≫ g ≫ f := by
    rw [Category.assoc, show k ≫ b = p ≫ f from pullback.condition,
      ← Category.assoc t, show t ≫ p = v ≫ g from pullback.condition, Category.assoc]
  have hfg : g ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away j.1))) := by
    change Spec.map (CommRingCat.ofHom (algebraMap (C i) (Localization.Away j.1))) ≫ f = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R (C i) _).symm)
  let q := pullback.lift (t ≫ k) v (hsq.trans (by rw [hfg]))
  obtain ⟨w, hw⟩ := hdom j
  have hq : (q ≫ w) ≫ affineBlowupπ (J i) = t ≫ p := by
    rw [Category.assoc, hw, ← Category.assoc, pullback.lift_snd]
    exact pullback.condition.symm
  change HasFlatPurePullbacks (t ≫ p) _ _
  rw [← hq]
  exact (hflat i).comp (q ≫ w)

end SerrePositivity.AlgebraicGeometry
