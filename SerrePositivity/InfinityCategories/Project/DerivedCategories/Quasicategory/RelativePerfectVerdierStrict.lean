module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeInvariant
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagramComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle

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

namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierDiagram
namespace SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativePerfectVerdierRectangle
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

namespace RelativePerfectVerdierDiagram

variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 既存の厳密商の相対証明書を、同じ四角形・恒等完備化で受ける。 -/
def ofStrict (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (ν ≫ perfectStableInfinityInclusion))
    : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram ν := by
  have hL := perfectStableObject_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν) 0 0)
  have hM := perfectStableObject_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν) 1 0)
  have hR := perfectStableObject_isIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν) 1 1)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 0 0)).obj at hL
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 1 0)).obj at hM
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ ν ≫ perfectStableInfinityInclusion) 1 1)).obj at hR
  rw [d.image_eq, d.image.left_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex] at hL
  rw [d.image_eq, d.image.middle_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex] at hM
  rw [d.image_eq, d.image.right_eq, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex] at hR
  let p : PerfectVerdierSequence.{u} := {
    verdier := d.image.toVerdierSequence
    left_complete := hL
    middle_complete := hM
    right := d.image.right
    completion := ⟨𝟙 d.image.right.obj, inferInstance⟩
    isCompletion := ⟨hR, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_id _, fun x => ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.refl x⟩⟩ }
  have hp : p.projection = d.image.projection := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (Category.comp_id _)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofSquare ν p d.square
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    rw [Category.assoc, Category.assoc, d.image_eq]
    exact d.image.bottom_edge.trans (perfectStableArrow_inclusion _ _ _).symm
  · apply (cancel_mono perfectStableInfinityInclusion).mp
    rw [Category.assoc, Category.assoc, d.image_eq, perfectStableArrow_inclusion, hp]
    exact d.image.right_edge
  · have h := d.zero_corner
    exact h

@[simp] lemma ofStrict_square
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (ν ≫ perfectStableInfinityInclusion)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStrict d).square = d.square := rfl

end RelativePerfectVerdierDiagram

namespace RelativePerfectVerdierRectangle

variable {S : SSet.{u + 1}} {ν : S ⟶ perfectStableInfinity.{u}}

/-- 既存の厳密長方形を、同じ全図式と恒等完備化を持つ特殊化として受ける。 -/
def ofStrict (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle (ν ≫ perfectStableInfinityInclusion)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle ν := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.ofActualFaces d.diagram (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStrict d.right)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierDiagram.ofStrict d.outer)
  · change d.right.square = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 0
    rw [d.right_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  · change d.outer.square = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare d.diagram 1
    rw [d.outer_eq, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

@[simp] lemma ofStrict_diagram
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierRectangle (ν ≫ perfectStableInfinityInclusion)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativePerfectVerdierRectangle.ofStrict d).diagram = d.diagram := rfl

end RelativePerfectVerdierRectangle
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
