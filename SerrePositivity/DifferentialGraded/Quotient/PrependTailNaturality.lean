module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaceEquations
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality

/-! # 先頭Hom合成と後方cochainの整合性

先頭の中間対象を保ったまま、それより後のtensor部分に任意次数cochainを作用させる場合を扱う。
先頭εを消す場合の結合則は別途必要である。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- prependMapは先頭の中間対象より後の任意次数cochainと可換する。 -/
lemma prependMap_tail_cochain {S : Set D} (c : S) (w w' : Word S) (x y z : D)
    (p : ℤ) (f : Cochain (epsilonComplex A ⊗ term A D w c.val z)
      (epsilonComplex A ⊗ term A D w' c.val z) p) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      ((tensorLeftHom (homObject A D x c.val) _ _).f p f) (zero_add p) =
    ((tensorLeftHom (homObject A D x y) _ _).f p
      ((tensorLeftHom (homObject A D y c.val) _ _).f p f)).comp
      (Cochain.ofHom (prependMap A D (c :: w') x y z)) (add_zero p) := by
  simpa only [prependMap, tensorHom_id] using
    tensorJoin_cochain_naturality (homObject A D x y) (homObject A D y c.val)
      (homObject A D x c.val) _ _ (eComp (Complex A) x y c.val) p f

end SerrePositivity.DifferentialGraded.DGQuotient
