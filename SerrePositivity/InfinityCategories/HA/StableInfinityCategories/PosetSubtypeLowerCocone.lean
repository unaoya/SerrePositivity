module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerKanShape
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveVertexExt
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitExistenceTransfer
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def posetSubtypeLowerCocone {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection T c) ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso T c
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T))
    (𝟙 (nerve P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).restrict e.hom
  refine ⟨d.val, d.property.trans ?_⟩
  change e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection _ _ ≫ (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) ≫ 𝟙 _)) = _
  rw [Category.comp_id, ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso_projection]

lemma posetSubtypeLowerCocone_vertex {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    (posetSubtypeLowerCocone T c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) (𝟙 (nerve P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).restrict (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso T c).hom).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone_vertex]
  rfl

lemma posetSubtypeLowerCocone_postcomp_val {P : Type u} [PartialOrder P]
    (T : P → Prop) (c : P) {X : SSet.{u}} (F : nerve P ⟶ X) :
    (posetSubtypeLowerCocone T c).val ≫ F =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).restrict
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso T c).hom).val := by
  simp only [posetSubtypeLowerCocone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone,
    Category.assoc, Category.comp_id]

lemma isColimit_posetSubtypeLowerCocone_of_canonical {P : Type u} [PartialOrder P]
    (T : P → Prop) (c : P) {X : SSet.{u}} (F : nerve P ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T))
      F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (posetSubtypeLowerCocone T c)) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) F (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerKanShapeIso T c).hom).mp h
  exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ (posetSubtypeLowerCocone_postcomp_val T c F)).mpr he

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
