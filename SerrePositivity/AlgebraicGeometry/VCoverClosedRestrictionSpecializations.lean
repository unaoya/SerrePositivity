module

public import SerrePositivity.AlgebraicGeometry.CompactOpenSpecialization
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverSpecializations
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
概要：v 判定と閉埋め込みで、指定開の特殊化を閉部分の像へ入れる。
方針：特殊化の鎖を持ち上げ、始点を含む閉部分が終点も含むことを使う。
規約：元の v 被覆に固有性・Noether 性を仮定しない。
使われ方：Rydh Proposition 3.7 の Z⊆V の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 指定開の逆像を含む閉部分は、その開の点の特殊化すべてを v 判定で覆う。 -/
theorem mem_range_comp_of_vCover_specialization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (hf : IsSchemeVCover f)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : Y.Opens)
    (hU : ∀ x : X, f x ∈ U → x ∈ Set.range i)
    {u y : Y} (hu : u ∈ U) (huy : u ⤳ y) : y ∈ Set.range (i ≫ f) := by
  obtain ⟨x, z, hxz, hxu, hzy⟩ := hf.liftsSpecializations huy
  have hx : x ∈ Set.range i := hU x (hxu.symm ▸ hu)
  have hz : z ∈ Set.range i := i.isClosedEmbedding.isClosed_range.stableUnderSpecialization hxz hx
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, by change f (i w) = y; rw [hw, hzy]⟩

/-- 指定開の逆像を含む閉部分は、その開の閉包全体を v 判定で覆う。 -/
theorem closure_subset_range_comp_of_vCover_closedRestriction
    {X Y Z : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) (hf : IsSchemeVCover f) (i : Z ⟶ X) [IsClosedImmersion i]
    (U : Y.Opens) (hUc : IsCompact (U : Set Y))
    (hU : ∀ x : X, f x ∈ U → x ∈ Set.range i) :
    closure (U : Set Y) ⊆ Set.range (i ≫ f) := by
  intro y hy
  obtain ⟨u, hu, huy⟩ := exists_specialization_from_compactOpen_closure U hUc hy
  exact mem_range_comp_of_vCover_specialization f hf i U hU hu huy

end SerrePositivity.AlgebraicGeometry
