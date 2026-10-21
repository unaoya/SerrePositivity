module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionRawChange
/-!
概要：元の出力分解と変更同型の指定値を、同じ raw 出力射影へ回収する。
方針：出力宇宙の上げ下げと指定出力比較の後合成則だけを使う。
規約：元の入力切断と変更比較を保持。使われ方：導来射作用との共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
variable {F G : DGFunctor R C (RightModule R E)}
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (hs : ∀ x, moduleDegreewiseSurjective R E (a x))
  (hq : ∀ x, moduleQuasiIso R E (a x))
  (ha : ∀ x y, F.map x y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
      (ForgetEnrichment.of (Complex R) (G.obj y)))
lemma dgModuleResolvedInfinity_changeIso_unfold_heq :
    HEq (dgModuleResolvedInfinity_changeIso R C E a hs hq ha)
      (((dgModuleOutputResolution_changeIso R C E a hs hq ha).precomp
        (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))).postcomp
        (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
          (SemifreeDGModules R E)))) := by
  simp only [dgModuleResolvedInfinity_changeIso, Eq.mp]
  rfl
lemma dgModuleResolvedInfinity_changeIso_raw_heq :
    HEq (dgModuleResolvedInfinity_changeIso R C E a hs hq ha)
      ((dgModuleOutputResolution_rawChangeIso R C E a hs hq ha).precomp
        (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))) := by
  have h₀ := dgModuleResolvedInfinity_changeIso_unfold_heq R C E a hs hq ha
  have h₁ := heq_of_eq (F2.functorIso_precomp_postcomp
    (dgModuleOutputResolution_changeIso R C E a hs hq ha)
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
    (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))))
  have h₂ := F2.functorIso_precomp_heq_of_heq
    (dgModuleOutputResolution_rawChangeIso R C E a hs hq ha)
    ((dgModuleOutputResolution_changeIso R C E a hs hq ha).postcomp
      (dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E))))
    (dgModuleOutputResolutionInfinity_down_eq R C E F).symm
    (dgModuleOutputResolutionInfinity_down_eq R C E G).symm
    (dgModuleOutputResolution_changeIso_down_heq R C E a hs hq ha)
    (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C))
  exact h₀.trans (h₁.trans h₂)
end SerrePositivity.InfinityCategories
