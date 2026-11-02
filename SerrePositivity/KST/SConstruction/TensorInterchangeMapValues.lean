module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-! # tensor 交差後の二つの射の全斉次値
概要：四つの純斉次成分の交差と二つの chain map の値を、一つの式へ束ねる。
方針：元の tensorμ の交差符号と tensor 射の成分式を使う。
規約：中央二次数の Koszul 符号を保持する。使われ方：Serre 対角と connection の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 元の tensor 交差後の二射は、中央二因子の符号と同じ二つの値を回収する。 -/
lemma tensorInterchangeMap_apply {A : Type u} [CommRing A]
    {P Q T U X Y : Complex A} (f : P ⊗ T ⟶ X) (g : Q ⊗ U ⟶ Y)
    (i j k l n : ℤ) (hn : (i + j) + (k + l) = n)
    (a : P.X i) (b : Q.X j) (c : T.X k) (d : U.X l) :
    (f ⊗ₘ g).f n ((tensorμ P Q T U).f n
      (ιTensorObj (P ⊗ Q) (T ⊗ U) (i + j) (k + l) n hn
        (ιTensorObj P Q i j (i + j) rfl (a ⊗ₜ[A] b) ⊗ₜ[A]
          ιTensorObj T U k l (k + l) rfl (c ⊗ₜ[A] d)))) =
      (j * k).negOnePow • ιTensorObj X Y (i + k) (j + l) n (by omega)
        (f.f (i + k) (ιTensorObj P T i k (i + k) rfl (a ⊗ₜ[A] c)) ⊗ₜ[A]
          g.f (j + l) (ιTensorObj Q U j l (j + l) rfl (b ⊗ₜ[A] d))) := by
  change (f ⊗ₘ g).f n ((tensorμ P Q T U).f n
    (SerrePositivity.cochainTensorQuadι P Q T U i j k l n (by omega)
      ((a ⊗ₜ[A] b) ⊗ₜ[A] (c ⊗ₜ[A] d)))) = _
  rw [tensorμ_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [SerrePositivity.cochainTensorQuadι_apply]
  exact congrArg (fun t : (X ⊗ Y).X n => ((j * k).negOnePow : ℤ) • t)
    (tensorMap_apply f g (i + k) (j + l) n (by omega)
      (ιTensorObj P T i k (i + k) rfl (a ⊗ₜ[A] c))
      (ιTensorObj Q U j l (j + l) rfl (b ⊗ₜ[A] d)))

/-- 中間二次数の表示を任意に指定しても、同じ signed 交差の値を回収する。 -/
lemma tensorInterchangeMap_apply_of_sums {A : Type u} [CommRing A]
    {P Q T U X Y : Complex A} (f : P ⊗ T ⟶ X) (g : Q ⊗ U ⟶ Y)
    (i j k l p q n : ℤ) (hp : i + j = p) (hq : k + l = q) (hn : p + q = n)
    (a : P.X i) (b : Q.X j) (c : T.X k) (d : U.X l) :
    (f ⊗ₘ g).f n ((tensorμ P Q T U).f n
      (ιTensorObj (P ⊗ Q) (T ⊗ U) p q n hn
        (ιTensorObj P Q i j p hp (a ⊗ₜ[A] b) ⊗ₜ[A]
          ιTensorObj T U k l q hq (c ⊗ₜ[A] d)))) =
      (j * k).negOnePow • ιTensorObj X Y (i + k) (j + l) n (by omega)
        (f.f (i + k) (ιTensorObj P T i k (i + k) rfl (a ⊗ₜ[A] c)) ⊗ₜ[A]
          g.f (j + l) (ιTensorObj Q U j l (j + l) rfl (b ⊗ₜ[A] d))) := by
  rcases hp with rfl
  rcases hq with rfl
  exact tensorInterchangeMap_apply f g i j k l n hn a b c d

end SerrePositivity.KST.SConstruction
