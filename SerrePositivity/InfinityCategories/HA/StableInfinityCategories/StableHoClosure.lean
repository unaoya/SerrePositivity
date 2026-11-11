module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # 実安定閉包のホモトピー圏上の対象条件

概要：実頂点の安定閉包は h C 上で同型と distinguished triangle の三つの閉性を持つ。
方針：実 cofiber 表示へ戻し、実閉包の cofiber・fiber・拡大閉性を適用する。
規約：h C の三角構造は実 cofiber に由来する。使われ方：分母計算との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory Limits Pretriangulated SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 実安定閉包を h C の対象条件として読む。 -/
def stableHoClosure (P : Set (X _⦋0⦌)) : ObjectProperty (hoFunctor.obj X) :=
  fun a => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P a.as.as

omit [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] in
/-- 実頂点での対象条件は元の閉包条件そのもの。 -/
lemma stableHoClosure_mk (P : Set (X _⦋0⦌)) (x : X _⦋0⦌) :
    stableHoClosure P (SSet.HomotopyCategory.mk x) ↔ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure P x := Iff.rfl

/-- 実安定閉包は h C 上でも同型で閉じる。 -/
instance stableHoClosure_isClosedUnderIsomorphisms (P : Set (X _⦋0⦌)) :
    (stableHoClosure P).IsClosedUnderIsomorphisms where
  of_iso {a b} e ha := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_iso e ha

/-- 指定対象条件は実零頂点を含む。 -/
instance stableHoClosure_containsZero (P : Set (X _⦋0⦌)) :
    (stableHoClosure P).ContainsZero where
  exists_zero := ⟨SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex,
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero.isZeroHo,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_zero (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero⟩

/-- 三角形の後二対象が属すると、第一対象も属する。 -/
instance stableHoClosure_isTriangulatedClosed₁ (P : Set (X _⦋0⦌)) :
    (stableHoClosure P).IsTriangulatedClosed₁ := .mk' (by
  intro T hT h₁ h₂
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have ha := (stableHoClosure P).prop_of_iso (Triangle.π₂.mapIso e) h₁
  have hb := (stableHoClosure P).prop_of_iso (Triangle.π₃.mapIso e) h₂
  exact (stableHoClosure P).prop_of_iso (Triangle.π₁.mapIso e.symm)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_fiber t (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout t ht) ha hb))

/-- 三角形の両端が属すると、中間対象も属する。 -/
instance stableHoClosure_isTriangulatedClosed₂ (P : Set (X _⦋0⦌)) :
    (stableHoClosure P).IsTriangulatedClosed₂ := .mk' (by
  intro T hT h₁ h₂
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have ha := (stableHoClosure P).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hb := (stableHoClosure P).prop_of_iso (Triangle.π₃.mapIso e) h₂
  exact (stableHoClosure P).prop_of_iso (Triangle.π₂.mapIso e.symm)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.extension P t ht ha hb))

/-- 三角形の前二対象が属すると、第三対象も属する。 -/
instance stableHoClosure_isTriangulatedClosed₃ (P : Set (X _⦋0⦌)) :
    (stableHoClosure P).IsTriangulatedClosed₃ := .mk' (by
  intro T hT h₁ h₂
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have ha := (stableHoClosure P).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hb := (stableHoClosure P).prop_of_iso (Triangle.π₂.mapIso e) h₂
  exact (stableHoClosure P).prop_of_iso (Triangle.π₃.mapIso e.symm)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_cofiber t ht ha hb))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
