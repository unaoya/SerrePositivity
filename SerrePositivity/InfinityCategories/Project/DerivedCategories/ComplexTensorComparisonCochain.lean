module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-!
概要：全パラメータ複体の比較 cochain を左右 tensor し、実微分式を保つ。
方針：全 Hom の実鎖写像と、閉零射の tensor との厳密な比較を使う。
規約：片方の全パラメータだけを固定せず、任意の非有界複体を tensor する。
使われ方：出力分解 dg 圏の実合成の比較 cochain。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable {R : Type u} [CommRing R]
/-- 全 Hom の鎖写像への作用は、全整数次数の実 cochain の微分と可換。 -/
lemma complexHomMap_delta {P Q P' Q' : Complex R}
    (F : homComplex R P Q ⟶ homComplex R P' Q') (n m : ℤ) (h : Cochain P Q n) :
    δ n m (F.f n h) = F.f m (δ n m h) :=
  ConcreteCategory.congr_hom (F.comm n m) h
/-- 右 tensor した比較 cochain は、同じ実 tensor 射の微分式を満たす。 -/
lemma complexComparison_rightTensor_boundary {P Q : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0)
    (K : Complex R) :
    δ (-1) 0 ((tensorRightHom K P Q).f (-1) h) + Cochain.ofHom (f ▷ K) = 0 := by
  rw [complexHomMap_delta]
  have he := congrArg (fun t : Cochain P Q 0 ↦ (tensorRightHom K P Q).f 0 t) hh
  simpa only [map_add, map_zero, tensorRightHom_ofHom] using he
/-- 左 tensor も、同じ実 tensor 射の微分式を全パラメータで保つ。 -/
lemma complexComparison_leftTensor_boundary {P Q : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0)
    (K : Complex R) :
    δ (-1) 0 ((tensorLeftHom K P Q).f (-1) h) + Cochain.ofHom (K ◁ f) = 0 := by
  rw [complexHomMap_delta]
  have he := congrArg (fun t : Cochain P Q 0 ↦ (tensorLeftHom K P Q).f 0 t) hh
  simpa only [map_add, map_zero, tensorLeftHom_ofHom] using he
/-- 実鎖写像への後合成も、同じ比較 cochain の微分式を保つ。 -/
lemma complexComparison_postcompose_boundary {P Q T : Complex R}
    (h : Cochain P Q (-1)) (f : P ⟶ Q) (hh : δ (-1) 0 h + Cochain.ofHom f = 0)
    (g : Q ⟶ T) :
    δ (-1) 0 (h.comp (Cochain.ofHom g) (add_zero (-1))) + Cochain.ofHom (f ≫ g) = 0 := by
  rw [δ_comp_ofHom]
  have he := congrArg (fun t : Cochain P Q 0 ↦ t.comp (Cochain.ofHom g) (zero_add 0)) hh
  simpa only [Cochain.add_comp, Cochain.zero_comp, ← Cochain.ofHom_comp] using he
/-- 二つの実比較 cochain の和は、同じ二つの実差の和を比較する。 -/
lemma complexComparison_add_boundary {P Q : Complex R}
    (h₁ h₂ : Cochain P Q (-1)) (f₁ f₂ : P ⟶ Q)
    (hh₁ : δ (-1) 0 h₁ + Cochain.ofHom f₁ = 0)
    (hh₂ : δ (-1) 0 h₂ + Cochain.ofHom f₂ = 0) :
    δ (-1) 0 (h₁ + h₂) + Cochain.ofHom (f₁ + f₂) = 0 := by
  have hd : δ (-1) 0 (h₁ + h₂) = δ (-1) 0 h₁ + δ (-1) 0 h₂ := by
    exact map_add (((homComplex R P Q).d (-1) 0).hom) h₁ h₂
  rw [hd, Cochain.ofHom_add]
  calc
    _ = (δ (-1) 0 h₁ + Cochain.ofHom f₁) + (δ (-1) 0 h₂ + Cochain.ofHom f₂) := by abel
    _ = 0 := by rw [hh₁, hh₂, add_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
