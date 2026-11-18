module

public import SerrePositivity.HomologicalAlgebra.Complexes.NatTensor.Interchange

/-!
# 自然数鎖テンソルの比較射の斉次評価

概要：Berger–Fresse §1.1.4 の中間二因子の交換を実際の鎖同型として構成する。
方針：既存の結合子と符号付き交換を合成する。
規約：大域的な対称モノイダル instance は追加しない。
使われ方：shuffle と AW の余代数適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NatTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

open scoped _root_.TensorProduct

abbrev tensorMap {P P' Q Q' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') := HomologicalComplex.tensorHom f g

/-- 概要：結合子の順方向を斉次純テンソルで評価する（BF §1.1.4）。
方針：直和包含上の射の公式を純テンソルへ適用する。
規約：入力は左結合の三因子。
使われ方：四因子交換の評価。 -/
lemma associator_hom_apply_ι
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k n : ℕ) (h : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (HomologicalComplex.associator P Q T).hom.f n
      (ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T (i + j) k n h
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i (j + k) n (by omega)
      (x ⊗ₜ[A] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[A] z)) :=
  congrArg (fun f => f ((x ⊗ₜ[A] y) ⊗ₜ[A] z))
    (_root_.SerrePositivity.NatTensor.inclusion_associator_hom P Q T i j k n h)

/-- 概要：逆結合子を斉次純テンソルで評価する（BF §1.1.4）。
方針：逆方向の包含公式を純テンソルへ適用する。
規約：入力は右結合の三因子。
使われ方：四因子交換の評価。 -/
lemma associator_inv_apply_ι
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k n : ℕ) (h : i + j + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (HomologicalComplex.associator P Q T).inv.f n
      (ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i (j + k) n (by omega)
        (x ⊗ₜ[A] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[A] z))) =
    ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T (i + j) k n h
      ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[A] y) ⊗ₜ[A] z) :=
  congrArg (fun f => f (x ⊗ₜ[A] (y ⊗ₜ[A] z)))
    (_root_.SerrePositivity.NatTensor.inclusion_associator_inv P Q T i j k n h)

/-- 概要：中間全次数を指定した順結合子の評価（BF §1.1.4）。
方針：中間次数の等式を消去する。
規約：i+j=s を明示する。
使われ方：交換後の次数和の同定。 -/
lemma associator_hom_apply_ι_of_sum
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k s n : ℕ)
    (hs : i + j = s) (h : s + k = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (HomologicalComplex.associator P Q T).hom.f n
      (ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T s k n h
        ((ιTensorObj P Q i j s hs) (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i (j + k) n (by omega)
      (x ⊗ₜ[A] (ιTensorObj Q T j k (j + k) rfl) (y ⊗ₜ[A] z)) := by
  subst s
  exact _root_.SerrePositivity.NatTensor.associator_hom_apply_ι P Q T i j k n h x y z

/-- 概要：中間全次数を指定した逆結合子の評価（BF §1.1.4）。
方針：中間次数の等式を消去する。
規約：j+k=s を明示する。
使われ方：交換後の次数和の同定。 -/
lemma associator_inv_apply_ι_of_sum
    (P Q T : ChainComplex (ModuleCat.{u} A) ℕ) (i j k s n : ℕ)
    (hs : j + k = s) (h : i + s = n) (x : P.X i) (y : Q.X j) (z : T.X k) :
    (HomologicalComplex.associator P Q T).inv.f n
      (ιTensorObj P (_root_.SerrePositivity.NatTensor.tensor Q T) i s n h
        (x ⊗ₜ[A] (ιTensorObj Q T j k s hs) (y ⊗ₜ[A] z))) =
    ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) T (i + j) k n (by omega)
      ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[A] y) ⊗ₜ[A] z) := by
  subst s
  exact _root_.SerrePositivity.NatTensor.associator_inv_apply_ι P Q T i j k n (by omega) x y z

/-- 概要：テンソル鎖写像の斉次純テンソル上の評価（BF §1.1.4）。
方針：二変数全複体の包含公式を評価する。
規約：任意の全次数の同定を許す。
使われ方：比較写像の合成の計算。 -/
lemma tensorMap_apply_ι {P P' Q Q' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j n : ℕ) (h : i + j = n) (x : P.X i) (y : Q.X j) :
    (_root_.SerrePositivity.NatTensor.tensorMap f g).f n ((ιTensorObj P Q i j n h) (x ⊗ₜ[A] y)) =
      (ιTensorObj P' Q' i j n h) (f.f i x ⊗ₜ[A] g.f j y) :=
  congrArg (fun f => f (x ⊗ₜ[A] y)) (ι_mapBifunctorMap f g (curriedTensor _) (.down ℕ) i j n h)

/-- 概要：符号付き交換の斉次純テンソル上の評価（BF §1.1.4）。
方針：交換の包含公式を評価する。
規約：符号は (−1)^(ij)。
使われ方：四因子交換の中間段階。 -/
lemma symmetry_hom_apply_ι
    (P Q : ChainComplex (ModuleCat.{u} A) ℕ) (i j n : ℕ) (h : i + j = n)
    (x : P.X i) (y : Q.X j) :
    (_root_.SerrePositivity.NatTensor.symmetry P Q).hom.f n ((ιTensorObj P Q i j n h) (x ⊗ₜ[A] y)) =
      (-1 : ℤˣ) ^ (i * j) • ((ιTensorObj Q P j i n (by omega)) (y ⊗ₜ[A] x)) :=
  congrArg (fun f => f (x ⊗ₜ[A] y)) (_root_.SerrePositivity.NatTensor.inclusion_symmetry P Q i j n h)

abbrev tensorQuadι (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l n : ℕ) (h : i + j + k + l = n) :=
  (ιTensorObj P Q i j (i + j) rfl ⊗ₘ ιTensorObj T U k l (k + l) rfl) ≫
    ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) (i + j) (k + l) n (by omega)

/-- 概要：四重直和包含の純テンソル上の評価（BF §1.1.4）。
方針：二つの加群テンソルの射を評価する。
規約：左二因子・右二因子をそれぞれ含める。
使われ方：四因子交換の評価の始点と終点。 -/
lemma tensorQuadι_apply (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l n : ℕ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    _root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n h ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w)) =
      ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) (i + j) (k + l) n (by omega)
        ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[A] y) ⊗ₜ[A]
          (ιTensorObj T U k l (k + l) rfl) (z ⊗ₜ[A] w)) := rfl

/-- 概要：二つの全次数の同定を含む四重包含（BF §1.1.4）。
方針：中間全次数の等式を消去する。
規約：二つの次数和は独立に指定する。
使われ方：AW 対角の切断成分の移送。 -/
lemma tensorQuad_apply_of_sum (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l a b n : ℕ) (ha : i + j = a) (hb : k + l = b) (h : a + b = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) a b n h
      ((ιTensorObj P Q i j a ha) (x ⊗ₜ[A] y) ⊗ₜ[A]
        (ιTensorObj T U k l b hb) (z ⊗ₜ[A] w)) =
    _root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n (by omega)
      ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w)) := by
  subst a
  subst b
  rfl

set_option maxHeartbeats 1000000 in
-- 五つの全複体比較の合成を同時に簡約するため。
/-- 概要：四因子交換の斉次純テンソル上の評価（BF §1.1.4）。
方針：五つの結合子・交換の評価公式を合成する。
規約：符号は中間二因子の次数積。
使われ方：四重包含上の射の等式。 -/
lemma interchange_hom_apply_ι
    (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l n : ℕ) (h : i + j + k + l = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) (w : U.X l) :
    (_root_.SerrePositivity.NatTensor.interchange P Q T U).hom.f n
      (_root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n h ((x ⊗ₜ[A] y) ⊗ₜ[A] (z ⊗ₜ[A] w))) =
    (-1 : ℤˣ) ^ (j * k) •
      (_root_.SerrePositivity.NatTensor.tensorQuadι P T Q U i k j l n (by omega) ((x ⊗ₜ[A] z) ⊗ₜ[A] (y ⊗ₜ[A] w))) := by
  change (HomologicalComplex.associator P T (_root_.SerrePositivity.NatTensor.tensor Q U)).inv.f n
    ((_root_.SerrePositivity.NatTensor.tensorMap (𝟙 P) (HomologicalComplex.associator T Q U).hom).f n
      ((_root_.SerrePositivity.NatTensor.tensorMap (𝟙 P)
        (_root_.SerrePositivity.NatTensor.tensorMap (_root_.SerrePositivity.NatTensor.symmetry Q T).hom (𝟙 U))).f n
        ((_root_.SerrePositivity.NatTensor.tensorMap (𝟙 P) (HomologicalComplex.associator Q T U).inv).f n
          ((HomologicalComplex.associator P Q (_root_.SerrePositivity.NatTensor.tensor T U)).hom.f n
            (ιTensorObj (_root_.SerrePositivity.NatTensor.tensor P Q) (_root_.SerrePositivity.NatTensor.tensor T U) (i + j) (k + l) n (by omega)
              ((ιTensorObj P Q i j (i + j) rfl) (x ⊗ₜ[A] y) ⊗ₜ[A]
                (ιTensorObj T U k l (k + l) rfl) (z ⊗ₜ[A] w))))))) = _
  rw [_root_.SerrePositivity.NatTensor.associator_hom_apply_ι P Q (_root_.SerrePositivity.NatTensor.tensor T U) i j (k + l) n (by omega)]
  rw [_root_.SerrePositivity.NatTensor.tensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [_root_.SerrePositivity.NatTensor.associator_inv_apply_ι Q T U j k l (j + (k + l)) (by omega)]
  rw [_root_.SerrePositivity.NatTensor.tensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [_root_.SerrePositivity.NatTensor.tensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [_root_.SerrePositivity.NatTensor.tensorMap_apply_ι]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  rw [_root_.SerrePositivity.NatTensor.symmetry_hom_apply_ι]
  simp only [Units.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  rw [_root_.SerrePositivity.NatTensor.associator_hom_apply_ι_of_sum T Q U k j l (j + k) (j + (k + l))
    (by omega) (by omega)]
  rw [_root_.SerrePositivity.NatTensor.associator_inv_apply_ι_of_sum P T (_root_.SerrePositivity.NatTensor.tensor Q U)
    i k (j + l) (j + (k + l)) n (by omega) (by omega)]
  rw [_root_.SerrePositivity.NatTensor.tensorQuadι_apply]

/-- 概要：四因子交換の四重包含上の射の公式（BF §1.1.4）。
方針：四重純テンソルの外延性で評価公式を使う。
規約：中間二因子 j,k の符号を付ける。
使われ方：AW と shuffle の余代数適合性。 -/
@[reassoc]
lemma ιTensorQuad_interchange_hom
    (P Q T U : ChainComplex (ModuleCat.{u} A) ℕ)
    (i j k l n : ℕ) (h : i + j + k + l = n) :
    _root_.SerrePositivity.NatTensor.tensorQuadι P Q T U i j k l n h ≫ (_root_.SerrePositivity.NatTensor.interchange P Q T U).hom.f n =
    (-1 : ℤˣ) ^ (j * k) •
      (tensorμ (P.X i) (Q.X j) (T.X k) (U.X l) ≫
        _root_.SerrePositivity.NatTensor.tensorQuadι P T Q U i k j l n (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_fourfold'
  intro x y z w
  exact _root_.SerrePositivity.NatTensor.interchange_hom_apply_ι P Q T U i j k l n h x y z w

end SerrePositivity.NatTensor
