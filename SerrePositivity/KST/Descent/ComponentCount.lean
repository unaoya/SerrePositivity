module

public import SerrePositivity.KST.Descent.ComponentRemainderCover
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# 閉被覆からの既約成分数の減少

## 概要
有限な既約閉被覆の項数で既約成分数を抑え、残りの閉和自身の成分数が減ることを示す。

## 方針
各既約成分は被覆の一項と等しい。その項を選んで添字への単射を構成する。

## 規約
被覆の元の成分と新しい対象の成分を同一視せず、実際の個数の不等式を証明する。

## 使われ方
論文 補題 3.3・定理 3.1 の可約な基底に対する強い帰納。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

/-- 概要：有限な既約閉被覆の項数は既約成分数以上（論文 補題 3.3）。
方針：既約成分を含む被覆の一項を選び、極大性で等式を得る。
規約：空の空間と空の被覆も含み、空間の Noether 性は要求しない。
使われ方：残りの閉和の成分数を実際に減らす。 -/
theorem irreducibleComponents_card_le_of_closed_cover {X I : Type*}
    [TopologicalSpace X] [Finite I] (pieces : I → Set X)
    (closed : ∀ i, IsClosed (pieces i)) (irreducible : ∀ i, IsIrreducible (pieces i))
    (covering : ⋃ i, pieces i = Set.univ) :
    Nat.card (irreducibleComponents X) ≤ Nat.card I := by
  classical
  let := Fintype.ofFinite I
  have exists_piece (W : irreducibleComponents X) : ∃ i : I, W.val = pieces i := by
    have covered : W.val ⊆ ⋃₀ (↑(Finset.univ.image pieces) : Set (Set X)) := by
      intro x _
      have hx : x ∈ ⋃ i, pieces i := covering.symm ▸ Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_sUnion.mpr ⟨pieces i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩
    obtain ⟨D, hD, hWD⟩ := isIrreducible_iff_sUnion_isClosed.mp W.property.1
      (Finset.univ.image pieces)
      (by intro D hD; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD; exact closed i) covered
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hD
    exact ⟨i, hWD.antisymm (W.property.2 (irreducible i) hWD)⟩
  choose index agrees using exists_piece
  apply Nat.card_le_card_of_injective index
  intro U W same
  apply Subtype.ext
  exact (agrees U).trans ((congrArg pieces same).trans (agrees W).symm)

/-- 概要：残りの被約閉和自身の既約成分数は元より少ない（論文 定理 3.1）。
方針：他の整成分による実際の閉被覆で成分数を抑え、除いた一成分の分だけ減らす。
規約：新しい対象の成分との同型を仮定しない。
使われ方：次元を固定した既約成分数の強い帰納。 -/
theorem componentRemainder_componentCount_lt {S : Scheme.{u}} (X : FiniteTypeSchemes S)
    [NoetherianSpace X.obj.left] (c : IrreducibleComponentIndex X) :
    Nat.card (IrreducibleComponentIndex
      (reducedClosedAsFiniteType X (componentRemainder X c))) <
        Nat.card (IrreducibleComponentIndex X) := by
  classical
  let I := {d : IrreducibleComponentIndex X // d ≠ c}
  have bound : Nat.card (IrreducibleComponentIndex
      (reducedClosedAsFiniteType X (componentRemainder X c))) ≤ Nat.card I := by
    apply irreducibleComponents_card_le_of_closed_cover
      (fun d : I ↦ Set.range (componentToRemainder X c d.val d.property).hom.left)
    · intro d
      exact (componentToRemainder X c d.val d.property).hom.left.isClosedEmbedding.isClosed_range
    · intro d
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ (integralComponent X d.val).obj.left).image
          (componentToRemainder X c d.val d.property).hom.left
          (componentToRemainder X c d.val d.property).hom.left.continuous.continuousOn
    · exact componentToRemainder_covering X c
  let := Fintype.ofFinite (IrreducibleComponentIndex X)
  let := Fintype.ofFinite I
  have smaller : Nat.card I < Nat.card (IrreducibleComponentIndex X) := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_subtype_lt (p := fun d : IrreducibleComponentIndex X ↦ d ≠ c) (not_not.mpr rfl))
  exact bound.trans_lt smaller

end SerrePositivity.KST.Descent
