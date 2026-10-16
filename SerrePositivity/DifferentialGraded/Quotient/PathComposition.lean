module
public import SerrePositivity.DifferentialGraded.Quotient.PathUniversal

/-! # 有限path tensor項の連結

内部微分に関するchain mapを構成する。最終dg商のε消去微分との両立や結合則は後続で検証する。
Homの合成には主モデルの豊穣合成を使い、εを含むtensor因子の順序を保つ。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元のHomをpathの先頭Homと豊穣合成する。 -/
def prependMap {S : Set D} : ∀ (w : Word S) (x y z : D),
    homObject A D x y ⊗ term A D w y z ⟶ term A D w x z
  | [], x, y, z => eComp (Complex A) x y z
  | b :: w, x, y, z =>
    (α_ (homObject A D x y) (homObject A D y b.val)
      (epsilonComplex A ⊗ term A D w b.val z)).inv ≫
      (eComp (Complex A) x y b.val ⊗ₘ 𝟙 (epsilonComplex A ⊗ term A D w b.val z))

@[simp] lemma prependMap_nil (S : Set D) (x y z : D) :
    prependMap A D ([] : Word S) x y z = eComp (Complex A) x y z := rfl

/-- 二つのpathの連結。境界に隣接するHomだけを豊穣合成する。 -/
def appendMap {S : Set D} : ∀ (w z : Word S) (x y t : D),
    term A D w x y ⊗ term A D z y t ⟶ term A D (w ++ z) x t
  | [], z, x, y, t => prependMap A D z x y t
  | b :: w, z, x, y, t =>
    (α_ (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
      (term A D z y t)).hom ≫
    (homObject A D x b.val) ◁
      ((α_ (epsilonComplex A) (term A D w b.val y) (term A D z y t)).hom ≫
        (epsilonComplex A) ◁ appendMap w z b.val y t)

@[simp] lemma appendMap_nil_left {S : Set D} (w : Word S) (x y z : D) :
    appendMap A D [] w x y z = prependMap A D w x y z := rfl

@[simp] lemma appendMap_nil_nil (S : Set D) (x y z : D) :
    appendMap A D ([] : Word S) [] x y z = eComp (Complex A) x y z := rfl

end SerrePositivity.DifferentialGraded.DGQuotient
