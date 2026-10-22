module
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeLowerKanShape
public import SerrePositivity.InfinityCategories.Stable.ThinNerveVertexExt
public import SerrePositivity.InfinityCategories.Stable.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：native 左 Kan の局所余極限を同じ下方余錐へ移す。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def posetSubtypeLowerCocone {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    JoinCocone (nerveMap (posetSubtypeLowerProjection T c) ≫
      nerveMap (posetSubtypeInclusion T)) := by
  let e := posetSubtypeLowerKanShapeIso T c
  let d := (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T))
    (𝟙 (nerve P)) (nerveVertex c)).restrict e.hom
  refine ⟨d.val, d.property.trans ?_⟩
  change e.hom ≫ (leftKanProjection _ _ ≫ (nerveMap (posetSubtypeInclusion T) ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Category.assoc]
  rw [posetSubtypeLowerKanShapeIso_projection]

lemma posetSubtypeLowerCocone_vertex {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    (posetSubtypeLowerCocone T c).vertex = nerveVertex c := by
  change ((leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) (𝟙 (nerve P))
    (nerveVertex c)).restrict (posetSubtypeLowerKanShapeIso T c).hom).vertex = _
  rw [JoinCocone.vertex_restrict, leftKanCanonicalCocone_vertex]
  rfl

lemma posetSubtypeLowerCocone_postcomp_val {P : Type u} [PartialOrder P]
    (T : P → Prop) (c : P) {X : SSet.{u}} (F : nerve P ⟶ X) :
    (posetSubtypeLowerCocone T c).val ≫ F =
      ((leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) F (nerveVertex c)).restrict
        (posetSubtypeLowerKanShapeIso T c).hom).val := by
  simp only [posetSubtypeLowerCocone, JoinCocone.restrict, leftKanCanonicalCocone,
    Category.assoc, Category.comp_id]

lemma isColimit_posetSubtypeLowerCocone_of_canonical {P : Type u} [PartialOrder P]
    (T : P → Prop) (c : P) {X : SSet.{u}} (F : nerve P ⟶ X)
    (h : IsColimitCone (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T))
      F (nerveVertex c))) : IsColimitCone (mapJoinCocone F (posetSubtypeLowerCocone T c)) := by
  have he := (isColimitCone_iff_restrict_of_isIso
    (leftKanCanonicalCocone (nerveMap (posetSubtypeInclusion T)) F (nerveVertex c))
    (posetSubtypeLowerKanShapeIso T c).hom).mp h
  exact (isColimitCone_iff_of_val_eq _ _ (posetSubtypeLowerCocone_postcomp_val T c F)).mpr he

end SerrePositivity.InfinityCategories
