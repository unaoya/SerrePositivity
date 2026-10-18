module

public import SerrePositivity.KST.Descent.IrreducibleComponents
public import SerrePositivity.KST.Descent.ClosedCoverGeometry
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Data.Set.Card

/-!
# 一つの既約成分と残りの閉和

## 概要
Noether スキームを一つの整な成分と残りの被約閉部分に分け、交わりで次元を下げる。

## 方針
残りの台は他の既約成分の有限和とし、既約成分の極大性から真閉性を示す。

## 規約
交わりは実際の引き戻しであり、その被約性は要求しない。

## 使われ方
論文 補題 3.3・定理 3.1 の次元帰納と有限閉和の貼り合わせ。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} (X : FiniteTypeSchemes S) [NoetherianSpace X.obj.left]

/-- 概要：一つの既約成分を除いた残りの閉和の台（論文 定理 3.1）。
方針：他の既約成分の有限和の閉性を使う。
規約：成分が一つの場合、残りは空。
使われ方：一成分を取り出す二つの閉部分の被覆。 -/
noncomputable def componentRemainder (c : IrreducibleComponentIndex X) : Closeds X.obj.left :=
  ⟨⋃₀ (irreducibleComponents X.obj.left \ {c.val}),
    NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_sUnion
      (fun _ h ↦ isClosed_of_mem_irreducibleComponents _ h.1)⟩

/-- 概要：一つの既約成分は他の成分の有限和に含まれない（論文 定理 3.1）。
方針：既約な閉集合の有限被覆と既約成分の極大性を使う。
規約：残りが空の場合も含む。
使われ方：交わりの真閉性と次元低下。 -/
theorem irreducibleComponent_not_le_remainder (c : IrreducibleComponentIndex X) :
    ¬ irreducibleComponentClosedSet X c ≤ componentRemainder X c := by
  intro h
  have member := mem_of_subset_sUnion_irreducibleComponents c.val c.property
    (irreducibleComponents X.obj.left \ {c.val})
    NoetherianSpace.finite_irreducibleComponents.sdiff Set.sdiff_subset h
  exact member.2 (Set.mem_singleton c.val)

/-- 概要：残りの閉和は元の対象の真閉部分（論文 定理 3.1）。
方針：全体なら選んだ成分も含むことになり、極大性から得た非包含に反する。
規約：選んだ成分が一つある場合の主張で、空スキームを除外する仮定は追加しない。
使われ方：有限閉和の帰納を残りの部分へ進める。 -/
theorem componentRemainder_ne_top (c : IrreducibleComponentIndex X) :
    componentRemainder X c ≠ ⊤ := by
  intro h
  apply irreducibleComponent_not_le_remainder X c
  rw [h]
  exact le_top

omit [NoetherianSpace X.obj.left] in
/-- 概要：既約でない対象では選んだ整成分の像も真閉（論文 定理 3.1）。
方針：像が全体なら既約成分の既約性が全空間の既約性を与える。
規約：元の対象が既約でないことを明示する。
使われ方：閉和の両側が真閉部分になる帰納段階。 -/
theorem integralComponentInclusion_range_ne_univ (c : IrreducibleComponentIndex X)
    (reducible : ¬ IrreducibleSpace X.obj.left) :
    Set.range (integralComponentInclusion X c).hom.left ≠ Set.univ := by
  rw [range_integralComponentInclusion]
  intro h
  apply reducible
  apply (irreducibleSpace_def X.obj.left).mpr
  change IsIrreducible (Set.univ : Set X.obj.left)
  simpa only [h] using c.property.1

/-- 概要：残りの閉和を覆う既約成分の数は一つ減る（論文 定理 3.1）。
方針：有限集合から、その元である選んだ成分を除く。
規約：残りを覆う元の成分の数を比較し、新しいスキームの成分との同定は要求しない。
使われ方：次元を固定した有限な閉被覆の個数に関する帰納。 -/
theorem componentRemainder_cover_card_lt (c : IrreducibleComponentIndex X) :
    (irreducibleComponents X.obj.left \ {c.val}).ncard <
      (irreducibleComponents X.obj.left).ncard :=
  Set.ncard_sdiff_singleton_lt_of_mem c.property NoetherianSpace.finite_irreducibleComponents

/-- 概要：一成分と残りの閉和は全体を覆う（論文 定理 3.1）。
方針：各点を含む既約成分が選んだ成分かどうかで分ける。
規約：空の残りを除外しない。
使われ方：閉和の貼り合わせの幾何条件。 -/
theorem componentRemainder_covering (c : IrreducibleComponentIndex X) :
    (c.val : Set X.obj.left) ∪ (componentRemainder X c : Set X.obj.left) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : irreducibleComponent x = c.val
  · exact Or.inl (h ▸ mem_irreducibleComponent)
  · exact Or.inr (Set.mem_sUnion.mpr ⟨irreducibleComponent x,
      ⟨irreducibleComponent_mem_irreducibleComponents x, by simpa using h⟩,
      mem_irreducibleComponent⟩)

/-- 概要：一成分と残りの被約閉部分の実際の閉包含は全体を覆う（論文 定理 3.1）。
方針：二つの包含の像を台と同定する。
規約：構造層を持つ有限型対象の包含を使う。
使われ方：構成済みの閉和の抽象 blowup と降下の貼り合わせ。 -/
theorem componentSplit_covering (c : IrreducibleComponentIndex X) :
    Set.range (integralComponentInclusion X c).hom.left ∪
      Set.range (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)).hom.left =
        Set.univ := by
  rw [range_integralComponentInclusion]
  change c.val ∪ Set.range (reducedClosedInclusion (componentRemainder X c)) = Set.univ
  rw [range_reducedClosedInclusion]
  exact componentRemainder_covering X c

/-- 概要：一成分と残りの閉和の実際の抽象 blowup 正方形（論文 補題 3.3）。
方針：二つの指定包含の被覆に閉和の構成を適用する。
規約：被約性は元の対象 X に明示する。
使われ方：構成済みの閉和の全次数降下の貼り合わせへの幾何入力。 -/
noncomputable def componentSplitBlowup [IsReduced X.obj.left]
    (c : IrreducibleComponentIndex X) : AbstractBlowupSquare S :=
  closedCoverAbstractBlowup (integralComponentInclusion X c)
    (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)) (componentSplit_covering X c)

/-- 概要：一成分と残りの交わりは成分の真閉部分（論文 定理 3.1）。
方針：第一射影の像の公式と、成分が残りに含まれないことを使う。
規約：非被約な交わりのまま点の像を判定する。
使われ方：実際の交わりの次元低下。 -/
theorem componentSplit_intersection_proper (c : IrreducibleComponentIndex X) :
    Set.range (closedImmersionSquare (integralComponentInclusion X c)
      (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c))).f₁₂.hom.left ≠
        Set.univ := by
  intro h
  change Set.range (pullback.fst (integralComponentInclusion X c).hom.left
    (reducedClosedInclusion (componentRemainder X c))) = Set.univ at h
  rw [Scheme.Pullback.range_fst, range_reducedClosedInclusion] at h
  apply irreducibleComponent_not_le_remainder X c
  intro x hx
  have hxrange : x ∈ Set.range (integralComponentInclusion X c).hom.left := by
    rw [range_integralComponentInclusion]
    exact hx
  obtain ⟨y, hy⟩ := hxrange
  have hyrest : (integralComponentInclusion X c).hom.left y ∈ componentRemainder X c := by
    exact Set.eq_univ_iff_forall.mp h y
  exact hy ▸ hyrest

/-- 概要：一成分と残りの実際の交わりは有限上界 d より次元が低い（論文 定理 3.1）。
方針：整な成分への真閉埋め込みとして、次元低下を適用する。
規約：交わりを被約化せず、元の対象の有限な次元上界を明示する。
使われ方：閉和の貼り合わせの交わりに対する外側の次元帰納。 -/
theorem componentSplit_intersection_dimension_lt_bound (c : IrreducibleComponentIndex X)
    (d : ℕ) (bound : topologicalKrullDim X.obj.left ≤ d) :
    topologicalKrullDim (closedImmersionPullback (integralComponentInclusion X c)
      (reducedClosedAsFiniteTypeInclusion X (componentRemainder X c))).obj.left < d := by
  let i := integralComponentInclusion X c
  let j := reducedClosedAsFiniteTypeInclusion X (componentRemainder X c)
  exact @closedImmersion_dimension_lt_bound (closedImmersionPullback i j).obj.left
    (integralComponent X c).obj.left inferInstance (closedImmersionSquare i j).f₁₂.hom.left
    (closedImmersionSquare_first_isClosedImmersion i j) (componentSplit_intersection_proper X c) d
    ((integralComponent_dimension_le X c).trans bound)

end SerrePositivity.KST.Descent
