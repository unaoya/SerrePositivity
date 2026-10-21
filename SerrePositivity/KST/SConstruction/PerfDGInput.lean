module
public import SerrePositivity.KST.SConstruction.BundledDGInput

/-! # 実 Perf の出力宇宙に合わせた厳密 dg 入力
概要：小さい dg 圏と厳密 dg 関手を、Perf の写像空間と coherent nerve に必要な宇宙へ移す。
方針：元の束を ULift で保持し、通常の射も元の厳密 dg 関手の ULift とする。
規約：元の対象・Hom・小ささの証拠を保持。使われ方：実 Perf の厳密単体的豊穣関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded

/-- 元の小さい dg 入力を、実 Perf の出力に必要な対象宇宙で保持する束。 -/
structure PerfDGInput (A : Type u) [CommRing A] where
  category : ULift.{u + 2} (SmallBundledDGCategory.{u, v} A)

variable (A : Type u) [CommRing A]

instance perfDGInputCoeSort : CoeSort (PerfDGInput.{u, v} A) (Type v) :=
  ⟨fun C => C.category.down.carrier⟩

instance perfDGInputEnrichment (C : PerfDGInput.{u, v} A) : DGCategory A C :=
  C.category.down.enrichment

instance perfDGInputSmall (C : PerfDGInput.{u, v} A) : Small.{u} C := C.category.down.small

/-- 元の小さい dg 圏を、対象と全 Hom を変えずに出力宇宙の入力へ移す。 -/
def perfDGInputOf (C : Type v) [DGCategory A C] [Small.{u} C] : PerfDGInput.{u, v} A :=
  ⟨ULift.up (smallBundledDGCategoryOf A C)⟩

/-- 出力宇宙での通常の射は、元の厳密 dg 関手の ULift。 -/
instance perfDGInputCategory : Category.{max (u + 1) v} (PerfDGInput.{u, v} A) where
  Hom C D := ULift.{u + 1} (DGFunctor A C D)
  id C := ULift.up (DGFunctor.id C)
  comp F G := ULift.up (DGFunctor.comp F.down G.down)
  id_comp F := ULift.ext (strictDGFunctor_id_comp F.down)
  comp_id F := ULift.ext (strictDGFunctor_comp_id F.down)
  assoc F G H := ULift.ext (strictDGFunctor_comp_assoc F.down G.down H.down)

/-- 出力宇宙へ移した通常の射から、元の同じ厳密 dg 関手を回収する。 -/
def perfDGInputHomEquiv (C D : PerfDGInput.{u, v} A) : (C ⟶ D) ≃ DGFunctor A C D where
  toFun F := F.down
  invFun F := ULift.up F
  left_inv _ := rfl
  right_inv _ := rfl

/-- 出力宇宙での射の合成から、元の厳密 dg 関手の合成を厳密に回収する。 -/
lemma perfDGInputHomEquiv_comp {C D E : PerfDGInput.{u, v} A} (F : C ⟶ D) (G : D ⟶ E) :
    perfDGInputHomEquiv A C E (F ≫ G) =
      DGFunctor.comp (perfDGInputHomEquiv A C D F) (perfDGInputHomEquiv A D E G) := rfl

end SerrePositivity.KST.SConstruction
