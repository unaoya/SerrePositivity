module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomFactorization
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：分裂した射影と可換な次数一作用素の MC 方程式を商へ降ろす。
方針：射影による全 Hom の制限の単射性で判定し、微分・斉次合成の保存を使う。
規約：閉零射影の可換式を明示する一般補題。実 bar では退化列の検証からこの式を供給する。
使われ方：同じ theta から作る正規化 bar 微分の二乗零。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgCoherentBarHom_precompose_injective {M N P : ModuleCategory R D}
    (i : N ⟶ M) (p : M ⟶ N) (hip : i ≫ p = 𝟙 N) (q : ℤ) :
    Function.Injective ((eHomWhiskerRight (Complex R) p P).f q) := by
  intro z w h
  have ht := congrArg (fun a => (eHomWhiskerRight (Complex R) i P).f q a) h
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_precompose_comp R D, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_precompose_comp R D,
    hip, eHomWhiskerRight_id] at ht
  exact ht

lemma dgCoherentBarHom_postcompose_comp {M N P Q : ModuleCategory R D}
    (i : P ⟶ Q) {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) (h : p + q = n) :
    (eHomWhiskerLeft (Complex R) M i).f n
      (compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P) g f h) =
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) Q)
      ((eHomWhiskerLeft (Complex R) N i).f q g) f h := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) Q)
  intro x
  rw [moduleHomWhiskerLeft_apply_π, moduleHomCompose_π, moduleHomCompose_π,
    moduleHomWhiskerLeft_apply_π]
  exact Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ h

lemma dgCoherentBar_maurerCartan_of_split_projection {M N : ModuleCategory R D}
    (i : N ⟶ M) (p : M ⟶ N) (hip : i ≫ p = 𝟙 N)
    (θ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).X 1)
    (ψ : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N)).X 1)
    (hψ : (eHomWhiskerRight (Complex R) p N).f 1 ψ =
      (eHomWhiskerLeft (Complex R) M p).f 1 θ)
    (hθ : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).d 1 2 θ +
      compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) M)
        θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N)).d 1 2 ψ +
      compose R (x := ForgetEnrichment.to (Complex R) N)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) N)
        ψ ψ (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  apply dgCoherentBarHom_precompose_injective R D (M := M) (N := N) (P := N) i p hip 2
  rw [map_add, map_zero]
  have hp := ConcreteCategory.congr_hom
    ((eHomWhiskerRight (Complex R) p N).comm 1 2) ψ
  have hq := ConcreteCategory.congr_hom
    ((eHomWhiskerLeft (Complex R) M p).comm 1 2) θ
  change (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N)).d 1 2
      ((eHomWhiskerRight (Complex R) p N).f 1 ψ) =
    (eHomWhiskerRight (Complex R) p N).f 2
      ((moduleHom R D (ForgetEnrichment.to (Complex R) N)
        (ForgetEnrichment.to (Complex R) N)).d 1 2 ψ) at hp
  change (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N)).d 1 2
      ((eHomWhiskerLeft (Complex R) M p).f 1 θ) =
    (eHomWhiskerLeft (Complex R) M p).f 2
      ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) M)).d 1 2 θ) at hq
  rw [← hp, hψ, hq, moduleHomRestriction_compose R D, hψ,
    moduleHomClosedInsertion R D, hψ, ← dgCoherentBarHom_postcompose_comp R D]
  have h := congrArg (fun a => (eHomWhiskerLeft (Complex R) M p).f 2 a) hθ
  simpa only [map_add, map_zero] using h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
