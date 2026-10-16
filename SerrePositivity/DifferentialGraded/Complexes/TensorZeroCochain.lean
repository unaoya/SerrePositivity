module
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 閉性を仮定しない二つの次数0 cochainのtensor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma homComplexMap_differential {P Q R T : Complex A}
    (F : homComplex A P Q ⟶ homComplex A R T) (p q : ℤ) (f : Cochain P Q p) :
    δ p q (F.f p f) = F.f q (δ p q f) :=
  ConcreteCategory.congr_hom (F.comm p q) f

/-- 二つの次数0 cochainのtensor。どちらの閉性も必要としない。 -/
def tensorZeroCochain {P P' Q Q' : Complex A} (f : Cochain P P' 0) (g : Cochain Q Q' 0) :
    Cochain (P ⊗ Q) (P' ⊗ Q') 0 :=
  ((tensorRightHom Q P P').f 0 f).comp ((tensorLeftHom P' Q Q').f 0 g) (zero_add 0)

lemma tensorZeroCochain_ofHom {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorZeroCochain (Cochain.ofHom f) (Cochain.ofHom g) = Cochain.ofHom (f ⊗ₘ g) := by
  rw [tensorZeroCochain, tensorRightHom_ofHom, tensorLeftHom_ofHom,
    ← Cochain.ofHom_comp, ← tensorHom_def]

lemma tensorZeroCochain_apply {P P' Q Q' : Complex A} (f : Cochain P P' 0) (g : Cochain Q Q' 0)
    (i j n : ℤ) (hn : i + j = n) (x : P.X i) (y : Q.X j) :
    (tensorZeroCochain f g).v n n (add_zero n)
      (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
    ιTensorObj P' Q' i j n hn
      (f.v i i (add_zero i) x ⊗ₜ[A] g.v j j (add_zero j) y) := by
  rw [tensorZeroCochain, Cochain.comp_zero_cochain_v]
  change ((tensorLeftHom P' Q Q').f 0 g).v n n (add_zero n)
    (((tensorRightHom Q P P').f 0 f).v n n (add_zero n)
      (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y))) = _
  rw [tensorRightHom_apply_of_sum Q P P' 0 i j n i n hn (add_zero i) (add_zero n),
    tensorLeftHom_apply_of_sum P' Q Q' 0 i j n j n hn (add_zero j) (add_zero n)]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]

lemma tensorZeroCochain_differential {P P' Q Q' : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) :
    δ 0 1 (tensorZeroCochain f g) =
    ((tensorRightHom Q P P').f 0 f).comp
      ((tensorLeftHom P' Q Q').f 1 (δ 0 1 g)) (zero_add 1) +
    ((tensorRightHom Q P P').f 1 (δ 0 1 f)).comp
      ((tensorLeftHom P' Q Q').f 0 g) (add_zero 1) := by
  rw [tensorZeroCochain, δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1)]
  rw [homComplexMap_differential (tensorLeftHom P' Q Q') 0 1 g,
    homComplexMap_differential (tensorRightHom Q P P') 0 1 f]
  simp only [Int.negOnePow_zero, one_smul]

end SerrePositivity.DifferentialGraded
