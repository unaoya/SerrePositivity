module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableHoTriangulated

/-! # 実安定閉包の三角的生成性

概要：h C の実安定閉包は指定実頂点を含む最小の同型で閉じた三角的対象条件。
方針：実頂点の閉包の生成手順を帰納し、実 cofiber 三角形で三角閉性を適用する。
規約：retract 閉包は加えない。使われ方：有限 cell の分母条件との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Pretriangulated SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 任意の三角的対象条件への包含は、元の指定頂点だけで判定できる。 -/
theorem stableHoClosure_le_iff (P : Set (X _⦋0⦌))
    (Q : ObjectProperty (hoFunctor.obj X)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure P ≤ Q ↔ ∀ x ∈ P, Q (SSet.HomotopyCategory.mk x) := by
  constructor
  · intro h x hx
    exact h _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem hx)
  · intro h a ha
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x at ha
    induction ha with
    | of_mem hx => exact h _ hx
    | of_zero hx => exact Q.prop_of_isZero hx.isZeroHo
    | of_iso e _ ih => exact Q.prop_of_iso e ih
    | of_cofiber t ht _ _ ih₀ ih₁ =>
      exact Q.ext_of_isTriangulatedClosed₃ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t ht) ih₀ ih₁
    | of_fiber t ht _ _ ih₁ ih₂ =>
      have hc := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback t ht
      exact Q.ext_of_isTriangulatedClosed₁ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t hc)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles t hc) ih₁ ih₂

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
