module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# 一次数に集中した複体のホモトピー

## 概要
BF §1.1.2 の E(0) の収縮を厳密な同型へ移すため、一次数に集中した複体を扱う。

## 方針
ホモトピーの成分は異なる次数間の射なので零となる。ホモトピーの式から射の等式を得る。

## 規約
指定次数に自己ループを持たない任意の複体の形を使う。

## 使われ方
HA 3.2.4.7 の二つの包含を作る、零入力の増大の厳密な逆。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type*} {c : ComplexShape I} {j : I} {K L : HomologicalComplex C c}

/-- BF §1.1.2 の次数集中の下では、ホモトピーを持つ二射は等しい。 -/
lemma eq_of_homotopy_concentrated (hj : ¬ c.Rel j j)
    (hK : ∀ i, i ≠ j → IsZero (K.X i)) (hL : ∀ i, i ≠ j → IsZero (L.X i))
    {f g : K ⟶ L} (h : Homotopy f g) : f = g := by
  have hz : h.hom = 0 := by
    funext a b
    by_cases ha : a = j
    · subst a
      by_cases hb : b = j
      · subst b
        exact h.zero j j hj
      · exact (hL b hb).eq_of_tgt _ _
    · exact (hK a ha).eq_of_src _ _
  ext i
  have he := h.comm i
  rw [hz, map_zero, map_zero, zero_add, zero_add] at he
  exact he

/-- BF §1.1.2 の収縮は、両側が一次数に集中すれば指定射を保つ厳密な同型となる。 -/
def isoOfHomotopyEquivConcentrated (hj : ¬ c.Rel j j)
    (hK : ∀ i, i ≠ j → IsZero (K.X i)) (hL : ∀ i, i ≠ j → IsZero (L.X i))
    (e : HomotopyEquiv K L) : K ≅ L where
  hom := e.hom
  inv := e.inv
  hom_inv_id := eq_of_homotopy_concentrated hj hK hK e.homotopyHomInvId
  inv_hom_id := eq_of_homotopy_concentrated hj hL hL e.homotopyInvHomId

end SerrePositivity.EInfinity
