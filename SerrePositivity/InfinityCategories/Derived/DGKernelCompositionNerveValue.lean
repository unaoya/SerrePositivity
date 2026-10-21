module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTensorComposition
/-!
概要：元の通常 kernel 合成比較の指定値を、同じ結合子の実 nerve 像へ戻す。
方針：元の指定値と全 Hom 自然性を保持する実関手を使う。
規約：頂点成分の一致へ弱めない。使われ方：kernel の triangle・pentagon の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
private lemma alpha_mp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (c : γ) :
    HEq (Eq.mp h a) c ↔ HEq a c := by
  cases h
  rfl
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
/-- 元の通常合成比較は、同じ双加群結合子の逆の nerve 像を保持する。 -/
lemma dgKernelTensorCompositionNerveIso_heq (P : Bimodule R E D) (Q : Bimodule R F E) :
    HEq (dgKernelTensorCompositionNerveIso R D E F P Q)
      (dgBimoduleIsoNerve R F (RightModule R D)
        (BimoduleTensor.associatorIso R F E D (RightModule R D) Q P
          (DGFunctor.id (RightModule R D))).symm) := by
  simp only [dgKernelTensorCompositionNerveIso, alpha_mp_heq_iff]
  rfl
end SerrePositivity.InfinityCategories
