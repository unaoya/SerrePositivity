module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.Components

/-!
# 非負横次数から零延長した図式の射

## 概要
非負横次数で指定した射を、元の図式の零延長からの鎖写像へ延長する。

## 方針
非負の行では指定された零延長同型を使い、負の行では零射を使う。

## 規約
標的の負の行の零性は要求しない。境界で必要な零性は始域の零延長が持つ。

## 使われ方
BS 著者版 Lemma 4.22 の tensor–Hom 随伴による比較を、非負横次数の模型へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 非負行の指定射を、零延長の各整数行からの射へ延長する。 -/
def extendRowComponent (K : CochainComplex (Complex R) ℕ) (M : CochainComplex (Complex R) ℤ)
    (f : ∀ n : ℕ, K.X n ⟶ M.X (n : ℤ)) (i : ℤ) :
    (K.extend ComplexShape.embeddingUpNat).X i ⟶ M.X i :=
  if hi : 0 ≤ i then
    (K.extendXIso ComplexShape.embeddingUpNat (i := i.toNat)
      (Int.toNat_of_nonneg hi)).hom ≫ f i.toNat ≫
        eqToHom (congrArg M.X (Int.toNat_of_nonneg hi))
  else 0

/-- 非負行では、延長した成分は指定同型の後の元の射である。 -/
@[simp] theorem extendRowComponent_natCast (K : CochainComplex (Complex R) ℕ)
    (M : CochainComplex (Complex R) ℤ) (f : ∀ n : ℕ, K.X n ⟶ M.X (n : ℤ)) (n : ℕ) :
    extendRowComponent K M f (n : ℤ) =
      (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ f n := by
  dsimp only [extendRowComponent]
  rw [dif_pos (Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast, eqToHom_refl, Category.comp_id]

/-- 元の図式の零延長から、指定された行の射を成分に持つ鎖写像。 -/
def extendRowHom (K : CochainComplex (Complex R) ℕ) (M : CochainComplex (Complex R) ℤ)
    (f : ∀ n : ℕ, K.X n ⟶ M.X (n : ℤ))
    (hf : ∀ n : ℕ, f n ≫ M.d (n : ℤ) ((n + 1 : ℕ) : ℤ) = K.d n (n + 1) ≫ f (n + 1)) :
    K.extend ComplexShape.embeddingUpNat ⟶ M where
  f := extendRowComponent K M f
  comm' i j hij := by
    have hj : j = i + 1 := hij.symm
    subst j
    by_cases hi : 0 ≤ i
    · lift i to ℕ using hi
      have hs : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
      rw [hs, extendRowComponent_natCast, extendRowComponent_natCast]
      erw [K.extend_d_eq ComplexShape.embeddingUpNat (i := i) (j := i + 1) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun h => (K.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ h) (hf i)
    · exact (K.isZero_extend_X ComplexShape.embeddingUpNat i (fun n hn => by
        change (n : ℤ) = i at hn
        omega)).eq_of_src _ _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
