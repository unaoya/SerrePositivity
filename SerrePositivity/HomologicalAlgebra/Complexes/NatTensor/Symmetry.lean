module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.TensorComponents
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# 自然数鎖テンソルの Koszul 交換

概要：Berger–Fresse §1.1.4 の余代数のテンソルに必要な符号付き交換を構成する。
方針：二重複体の加群の交換を全複体の符号付き反転と合成する。
規約：自然数の鎖次数 p,q の交換符号は (−1)^(pq)。
使われ方：四重テンソルの中間二因子の交換と負次数比較の適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NatTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：自然数鎖の全複体の反転に用いる符号構造（BF §1.1.4）。
方針：次数和の交換則と (−1)^(pq) の微分との適合性を証明する。
規約：局所 instance としてのみ選択する。
使われ方：自然数鎖の実際の符号付き交換同型。 -/
@[instance_reducible] def shapeSymmetry :
    TotalComplexShapeSymmetry (.down ℕ) (.down ℕ) (.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    intro p p' h q
    obtain rfl : p = p' + 1 := h.symm
    change (-1 : ℤˣ) ^ ((p' + 1) * q) * 1 = (-1 : ℤˣ) ^ q * (-1 : ℤˣ) ^ (p' * q)
    rw [Nat.add_mul, Nat.one_mul, pow_add, mul_one, mul_comm]
  σ_ε₂ := by
    intro p q q' h
    obtain rfl : q = q' + 1 := h.symm
    change (-1 : ℤˣ) ^ (p * (q' + 1)) * (-1 : ℤˣ) ^ p = 1 * (-1 : ℤˣ) ^ (p * q')
    rw [Nat.mul_add, Nat.mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one, one_mul]

attribute [local instance] _root_.SerrePositivity.NatTensor.shapeSymmetry

/-- 概要：加群の交換を各二次数で適用する二重複体の同型（BF §1.1.4）。
方針：二つの方向に成分ごとの同型を作る。
規約：この段階では次数の符号を付けない。
使われ方：全複体の符号付き反転の前段。 -/
def bicomplexSymmetry (K L : ChainComplex (ModuleCat.{u} A) ℕ) :
    (((curriedTensor (ModuleCat A)).mapBifunctorHomologicalComplex
      (.down ℕ) (.down ℕ)).obj K).obj L ≅
      ((((curriedTensor (ModuleCat A)).flip).mapBifunctorHomologicalComplex
        (.down ℕ) (.down ℕ)).obj K).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents (fun q => β_ (K.X p) (L.X q)))

/-- 概要：自然数鎖テンソルの符号付き交換同型（BF §1.1.4）。
方針：加群の交換と全複体の反転同型を合成する。
規約：大域的なモノイダル instance を追加せず実際の同型を使う。
使われ方：余代数のテンソルの中間因子の交換。 -/
def symmetry (K L : ChainComplex (ModuleCat.{u} A) ℕ) :
    HomologicalComplex.tensorObj K L ≅ HomologicalComplex.tensorObj L K :=
  HomologicalComplex₂.total.mapIso (_root_.SerrePositivity.NatTensor.bicomplexSymmetry K L) (.down ℕ) ≪≫
    mapBifunctorFlipIso L K (curriedTensor (ModuleCat A)) (.down ℕ)

/-- 概要：符号付き交換の斉次包含上の公式（BF §1.1.4）。
方針：二重複体の交換と全複体の反転の包含公式を適用する。
規約：p+q=n の任意の全次数で述べる。
使われ方：四重テンソル交換の Koszul 符号を計算する。 -/
@[reassoc]
lemma inclusion_symmetry (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (_root_.SerrePositivity.NatTensor.symmetry K L).hom.f n =
      (-1 : ℤˣ) ^ (p * q) •
        ((β_ (K.X p) (L.X q)).hom ≫ ιTensorObj L K q p n (by omega)) := by
  change ιTensorObj K L p q n h ≫
    ((HomologicalComplex₂.total.map (_root_.SerrePositivity.NatTensor.bicomplexSymmetry K L).hom (.down ℕ)).f n ≫
      (mapBifunctorFlipIso L K (curriedTensor (ModuleCat A)) (.down ℕ)).hom.f n) = _
  rw [HomologicalComplex₂.ιTotal_map_assoc, ι_mapBifunctorFlipIso_hom]
  have hs : ComplexShape.σ (.down ℕ) (.down ℕ) (.down ℕ) q p =
      (-1 : ℤˣ) ^ (q * p) := rfl
  simp [_root_.SerrePositivity.NatTensor.bicomplexSymmetry, hs, mul_comm, Linear.comp_units_smul]

end SerrePositivity.NatTensor
