module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeInvariant
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierPullback
public import SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle

/-!
概要：従来の厳密相対図式を、恒等完備化による完備化付き版へ接続する。
方針：元の image_eq と二辺を保ち、完備性を持つ三対象に恒等完備化を使う。
規約：旧宣言の名前・型を変更しない。使われ方：既存の厳密版の特殊化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories.F2.Idempotent
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
namespace SerrePositivity.InfinityCategories.Derived.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

namespace RelativePerfectVerdierDiagram
open SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 既存の厳密商の相対証明書を、同じ四角形・恒等完備化で受ける。 -/
def ofStrict (d : RelativeVerdierDiagram (ν ≫ perfectStableInfinityInclusion))
    : RelativePerfectVerdierDiagram ν := by
  have hL := perfectStableObject_isIdempotentComplete (squareVertex (d.square ≫ ν) 0 0)
  have hM := perfectStableObject_isIdempotentComplete (squareVertex (d.square ≫ ν) 1 0)
  have hR := perfectStableObject_isIdempotentComplete (squareVertex (d.square ≫ ν) 1 1)
  change IsIdempotentComplete
    (stableObject (squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 0 0)).obj at hL
  change IsIdempotentComplete
    (stableObject (squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 1 0)).obj at hM
  change IsIdempotentComplete
    (stableObject (squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 1 1)).obj at hR
  rw [d.image_eq, d.image.left_eq, stableObject_vertex] at hL
  rw [d.image_eq, d.image.middle_eq, stableObject_vertex] at hM
  rw [d.image_eq, d.image.right_eq, stableObject_vertex] at hR
  let p : PerfectVerdierSequence.{u} := {
    verdier := d.image.toVerdierSequence
    left_complete := hL
    middle_complete := hM
    right := d.image.right
    completion := ⟨𝟙 d.image.right.obj, inferInstance⟩
    isCompletion := ⟨hR, isFullyFaithful_id _, fun x => ⟨x, IsVertexRetractOf.refl x⟩⟩ }
  have hp : p.projection = d.image.projection := ExactMap.ext (Category.comp_id _)
  apply ofSquare ν p d.square
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    rw [Category.assoc, Category.assoc, d.image_eq]
    exact d.image.bottom_edge.trans (perfectStableArrow_inclusion _ _ _).symm
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    rw [Category.assoc, Category.assoc, d.image_eq, perfectStableArrow_inclusion, hp]
    exact d.image.right_edge
  · have h := d.zero_corner
    exact h

@[simp] lemma ofStrict_square
    (d : RelativeVerdierDiagram (ν ≫ perfectStableInfinityInclusion)) :
    (ofStrict d).square = d.square := rfl

end RelativePerfectVerdierDiagram

namespace RelativePerfectVerdierRectangle
open SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 既存の厳密長方形を、同じ全図式と恒等完備化を持つ特殊化として受ける。 -/
def ofStrict (d : RelativeVerdierRectangle (ν ≫ perfectStableInfinityInclusion)) :
    RelativePerfectVerdierRectangle ν := by
  apply ofActualFaces d.diagram (RelativePerfectVerdierDiagram.ofStrict d.right)
    (RelativePerfectVerdierDiagram.ofStrict d.outer)
  · change d.right.square = (β_ _ _).hom ≫ pastingSquare d.diagram 0
    rw [d.right_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  · change d.outer.square = (β_ _ _).hom ≫ pastingSquare d.diagram 1
    rw [d.outer_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

@[simp] lemma ofStrict_diagram
    (d : RelativeVerdierRectangle (ν ≫ perfectStableInfinityInclusion)) :
    (ofStrict d).diagram = d.diagram := rfl

end RelativePerfectVerdierRectangle
end SerrePositivity.InfinityCategories.Derived.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict_square := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict_square

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofStrict (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofStrict := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofStrict

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofStrict_diagram := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofStrict_diagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_10 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_11 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_12 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_13 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_14 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_14

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_15 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_15

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram.ofStrict._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierDiagram.ofStrict._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofStrict._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofStrict._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle.ofStrict._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Quasicategory.RelativePerfectVerdierRectangle.ofStrict._proof_2
