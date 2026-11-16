module

public import SerrePositivity.HomologicalAlgebra.CochainProductTotalLinearComponents
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalDifferential
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ConcreteCategory

/-!
# 完備底変換と Tot の比較で使う成分の計算

## 概要
既存の積全複体の一つの成分への挿入と、行の完全性による原始元の存在を与える。

## 方針
同じ指定射影の線形同値を使う。内部次数には上にも下にも有界性を課さない。

## 規約
BS 著者版 Lemma 4.22 の鎖複体版の準備。ここではまだ底変換と Tot の可換性を主張しない。

## 使われ方
行ごとのホモロジーの下界から、積全複体の尾部の下界を証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.HomologicalAlgebra SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]
variable (K : CochainComplex (Complex R) ℕ)

/-- 既存の積全複体。成分の表示のために別の全複体を選ばない。 -/
abbrev total : Complex R := (cochainProductTotalizationFunctor (ModuleCat.{u} R)).obj K

/-- 全複体の元は指定成分で判定できる。 -/
theorem ext {q : ℤ} {x y : (total K).X q}
    (h : ∀ n, componentπ K n q x = componentπ K n q y) : x = y := by
  apply (componentsLinearEquiv K q).injective
  exact funext h

/-- 一行だけに成分を持つ元を、同じ積全複体へ挿入する。 -/
def insert (q : ℤ) (n : ℕ) (x : (K.X n).X (q-n)) : (total K).X q :=
  (componentsLinearEquiv K q).symm (Pi.single n x)

@[simp] theorem insert_component_self (q : ℤ) (n : ℕ) (x : (K.X n).X (q-n)) :
    componentπ K n q (insert K q n x) = x := by
  change (componentsLinearEquiv K q ((componentsLinearEquiv K q).symm (Pi.single n x))) n = x
  simp

@[simp] theorem insert_component_ne (q : ℤ) (n m : ℕ) (hm : m ≠ n)
    (x : (K.X n).X (q-n)) : componentπ K m q (insert K q n x) = 0 := by
  change (componentsLinearEquiv K q ((componentsLinearEquiv K q).symm (Pi.single n x))) m = 0
  simp [hm, Ne.symm hm]

/-- 零行では、全微分の指定成分は縦微分そのものである。 -/
theorem differential_zero (q : ℤ) (x : (total K).X q) :
    componentπ K 0 (q+1) ((total K).d q (q+1) x) =
      (K.X 0).d (q-0) (q+1-0) (componentπ K 0 q x) :=
  congrArg (fun f => f x) (component_d_zero K q)

/-- 正の行では、全微分の指定成分は横と縦の二項の和である。 -/
theorem differential_succ (q : ℤ) (n : ℕ) (x : (total K).X q) :
    componentπ K (n+1) (q+1) ((total K).d q (q+1) x) =
      (eqToHom (by congr 1; push_cast; omega) :
        (K.X (n+1)).X (q-n) ⟶ (K.X (n+1)).X (q+1-(n+1 : ℕ)))
        ((K.d n (n+1)).f (q-n) (componentπ K n q x)) +
      ((n+1 : ℕ) : ℤ).negOnePow •
        ((K.X (n+1)).d (q-(n+1 : ℕ)) (q+1-(n+1 : ℕ))
          (componentπ K (n+1) q x)) :=
  congrArg (fun f => f x) (component_d_succ K n q)

/-- 先行する成分が零なら、全余輪体の最初の成分は縦の余輪体となる。 -/
theorem first_component_closed (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0) (n : ℕ)
    (hprev : ∀ m : ℕ, m < n → componentπ K m q x = 0) :
    (K.X n).d (q-n) (q+1-n) (componentπ K n q x) = 0 := by
  cases n with
  | zero =>
    have h := differential_zero K q x
    rw [hx, map_zero] at h
    exact h.symm
  | succ n =>
    have h := differential_succ K q n x
    rw [hx, map_zero, hprev n (by omega), map_zero, map_zero, zero_add] at h
    exact (smul_eq_zero_iff_eq _).mp h.symm

/-- 行のホモロジーが零なら、縦の余輪体には同じ複体内の原始元がある。 -/
theorem exists_vertical_primitive (C : Complex R) (q : ℤ)
    (hC : IsZero (C.homology q)) (x : C.X q) (hx : C.d q (q+1) x = 0) :
    ∃ y : C.X (q-1), C.d (q-1) q y = x := by
  have he : C.ExactAt q := (HomologicalComplex.exactAt_iff_isZero_homology C q).mpr hC
  have hs : (C.sc' (q-1) q (q+1)).Exact :=
    (C.exactAt_iff' (q-1) q (q+1) (by simp) (by simp)).mp he
  exact (ShortComplex.moduleCat_exact_iff _).mp hs x hx

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
