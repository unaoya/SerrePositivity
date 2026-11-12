module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardCoefficients

/-!
# 標準二色語による Schur 射の検出

HA 3.2.4.7 の指定射の比較で、同時置換の関係を用いて標準語上の等式を全体へ延ばす。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (R : Type u) [CommRing R] (X Y : Complex R)

/-- 標準二色語を前合成して一致する Schur 射は、全体で一致する。 -/
lemma freeStandardSource_hom_ext {Z : Complex R}
    {f g : ((operad R).freeAlgebra (X ⊞ Y)).carrier ⟶ Z}
    (h : ∀ m n, freeStandardSource R X Y m n ≫ f =
      freeStandardSource R X Y m n ≫ g) : f = g := by
  apply schur_hom_ext R (sequence R) (X ⊞ Y) Z
  intro r
  apply (isColimitOfPreserves (tensorLeft ((operad R).arity r))
    (binaryTensorWordsIsColimit X Y r)).hom_ext
  rintro ⟨w⟩
  change ((operad R).arity r ◁ binaryTensorWordInclusion X Y r w) ≫
    schurι R (sequence R) (X ⊞ Y) r ≫ f =
      ((operad R).arity r ◁ binaryTensorWordInclusion X Y r w) ≫
        schurι R (sequence R) (X ⊞ Y) r ≫ g
  obtain ⟨m, n, hr, σ, _, _, hw⟩ := binaryTensorWord_standard_orbit r w
  subst r
  simp only [cast_eq] at hw
  subst w
  let C := (operad R).arity (m + n)
  let z := binaryTensorStandardPattern m n
  let e := binaryTensorWordPermutationIso X Y (m + n) σ z
  let a : C ⟶ C := (sequence R).map (FiniteBijection.permutation (m + n) σ)
  have he : (a ⊗ₘ e.hom) ≫ (C ◁ binaryTensorWordInclusion X Y (m + n) (σ • z)) =
      (C ◁ binaryTensorWordInclusion X Y (m + n) z) ≫
        (a ⊗ₘ (permutationAction (X ⊞ Y) (m + n) σ).asIso.hom) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun q => a ⊗ₘ q) (binaryTensorWordPermutationIso_inclusion X Y _ σ z)
  have hk (q : ((operad R).freeAlgebra (X ⊞ Y)).carrier ⟶ Z) :
      (a ⊗ₘ e.hom) ≫ (C ◁ binaryTensorWordInclusion X Y (m + n) (σ • z)) ≫
        schurι R (sequence R) (X ⊞ Y) (m + n) ≫ q =
      (C ◁ binaryTensorWordInclusion X Y (m + n) z) ≫
        schurι R (sequence R) (X ⊞ Y) (m + n) ≫ q := by
    rw [reassoc_of% he]
    rw [reassoc_of% schurι_diagonal R (sequence R) (X ⊞ Y) (m + n) σ]
  have ha : IsIso a := by dsimp [a]; infer_instance
  apply (cancel_epi (a ⊗ₘ e.hom)).1
  rw [hk f, hk g]
  apply (cancel_epi (C ◁ (binaryTensorStandardPowersIso X Y m n).inv)).1
  simpa only [freeStandardSource, whiskerLeft_comp, Category.assoc, C, z] using h m n

end SerrePositivity.EInfinity.BarrattEccles
