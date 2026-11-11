module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerComma

/-!
概要：左 Kan の実形状と具体的な下方射影を厳密に比較する。
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

def posetSubtypeLowerProjection {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c ⥤ {p : P // T p} where
  obj p := ⟨p.val, p.property.1⟩
  map f := homOfLE (leOfHom f)

def posetSubtypeLowerKanShapeIso {P : Type u} [PartialOrder P] (T : P → Prop) (c : P) :
    nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeCommaLowerNerveIso T c).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) c

lemma posetSubtypeLowerKanShapeIso_projection {P : Type u} [PartialOrder P]
    (T : P → Prop) (c : P) :
    (posetSubtypeLowerKanShapeIso T c).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) =
        nerveMap (posetSubtypeLowerProjection T c) := by
  dsimp only [posetSubtypeLowerKanShapeIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
