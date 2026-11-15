module
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
概要：非負鎖複体を負次数へ零延長したものからの斉次射を、元の鎖次数の成分で表示する。
方針：非正次数では指定延長同型で戻し、正次数では零対象の一意性を使う。
規約：次数 q の成分 n は Kₙ から H^(q-n) への射。有界性は仮定しない。
使われ方：HA 1.2.4、G10 の重みの end と Hom 複体の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits CochainComplex HomComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
variable (K : ChainComplex C ℕ) (H : CochainComplex C ℤ)

/-- 負の鎖次数への零延長を元の成分へ戻す指定同型。 -/
def negativeChainRowIso (n : ℕ) :
    (K.extend ComplexShape.embeddingDownNat).X (-(n : ℤ)) ≅ K.X n :=
  K.extendXIso ComplexShape.embeddingDownNat (i := n) rfl

/-- 斉次射から元の鎖次数 n の成分を取り出す。 -/
def extendedChainHomRows (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    K.X n ⟶ H.X (q-n) :=
  (negativeChainRowIso K n).inv ≫ z.v (-n) (q-n) (by omega)

/-- 元の鎖次数の成分を、零延長した重みからの斉次射へ戻す。 -/
def extendedChainHomRowsInverse (q : ℤ) (f : ∀ n : ℕ, K.X n ⟶ H.X (q-n)) :
    Cochain (K.extend ComplexShape.embeddingDownNat) H q :=
  Cochain.mk (fun p t h =>
    if hp : p ≤ 0 then
      (K.extendXIso ComplexShape.embeddingDownNat (i := (-p).toNat)
        (by change -(((-p).toNat : ℕ) : ℤ) = p; rw [Int.toNat_of_nonneg (by omega)]; omega)).hom ≫
      f (-p).toNat ≫ eqToHom (by congr 1; rw [Int.toNat_of_nonneg (by omega)]; omega)
    else 0)

/-- 同じ逆構成の非正次数での成分公式。 -/
theorem extendedChainHomRowsInverse_v (q : ℤ) (f : ∀ n : ℕ, K.X n ⟶ H.X (q-n))
    (n : ℕ) :
    (extendedChainHomRowsInverse K H q f).v (-n) (q-n) (by omega) =
      (negativeChainRowIso K n).hom ≫ f n := by
  simp [extendedChainHomRowsInverse, negativeChainRowIso,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]

/-- 元の鎖成分から戻して評価すると同じ成分になる。 -/
theorem extendedChainHomRows_inverse (q : ℤ) (f : ∀ n : ℕ, K.X n ⟶ H.X (q-n)) :
    extendedChainHomRows K H q (extendedChainHomRowsInverse K H q f) = f := by
  funext n
  dsimp only [extendedChainHomRows]
  rw [extendedChainHomRowsInverse_v, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 全斉次射は非正次数の成分から同じ零延長同型で復元できる。 -/
theorem extendedChainHomRowsInverse_rows (q : ℤ)
    (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) :
    extendedChainHomRowsInverse K H q (extendedChainHomRows K H q z) = z := by
  apply Cochain.ext
  intro p t h
  by_cases hp : p ≤ 0
  · have he : -(((-p).toNat : ℕ) : ℤ) = p := by
      rw [Int.toNat_of_nonneg (by omega)]; omega
    generalize hn : (-p).toNat = n at he
    subst p
    have ht : t = q-n := by omega
    cases ht
    rw [extendedChainHomRowsInverse_v]
    dsimp only [extendedChainHomRows]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat p
      (fun n hn => by change -(n : ℤ) = p at hn; omega)).eq_of_src _ _

/-- 斉次射の鎖次数の成分表示は係数環に線形な同値。 -/
def extendedChainHomRowsLinearEquiv (R : Type*) [Ring R] [Linear R C] (q : ℤ) :
    Cochain (K.extend ComplexShape.embeddingDownNat) H q ≃ₗ[R]
      (∀ n : ℕ, K.X n ⟶ H.X (q-n)) where
  toFun := extendedChainHomRows K H q
  invFun := extendedChainHomRowsInverse K H q
  left_inv := extendedChainHomRowsInverse_rows K H q
  right_inv := extendedChainHomRows_inverse K H q
  map_add' z w := by
    funext n
    simp only [extendedChainHomRows, Cochain.add_v, Pi.add_apply,
      Preadditive.comp_add]
  map_smul' r z := by
    funext n
    simp only [extendedChainHomRows, Cochain.smul_v, Pi.smul_apply,
      RingHom.id_apply, Linear.comp_smul]

end SerrePositivity.HomologicalAlgebra
