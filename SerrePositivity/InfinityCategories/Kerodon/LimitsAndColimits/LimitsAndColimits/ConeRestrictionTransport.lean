module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinSliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeMappingSpace

/-!
概要：図式の表示の等式を保持した錐の制限と、指定頂点上の制限を正規化する。
方針：slice の制限に図式の等式の移送を合成し、元の射影と uncurry を保つ。
規約：元の頂点・全単体を保持。使われ方：形状の pushout 上の錐空間の接着。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {A C X : SSet.{u}} {p : A ⟶ X} (F : C ⟶ X) (i : A ⟶ C) (hi : i ≫ F = p)

/-- 共通部分の図式の表示を移した、元の錐の制限。 -/
def normalizedConeRestriction : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict F i ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hi)

/-- 図式の表示を移した制限は元の頂点への射影を保つ。 -/
lemma normalizedConeRestriction_projection :
    normalizedConeRestriction F i hi ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F := by
  have ht {a b : A ⟶ X} (h : a = b) :
      eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a := by
    cases h
    exact Category.id_comp _
  rw [normalizedConeRestriction, Category.assoc, ht hi, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanSliceOverRestrict_projection]

/-- 正規化した制限も uncurry 後には元の形状の制限そのものである。 -/
lemma normalizedConeRestriction_uncurry {T : SSet.{u}} (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (a ≫ normalizedConeRestriction F i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 T) i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry a := by
  cases hi
  simp only [normalizedConeRestriction, eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_restrict a i

/-- 共通部分の元の図式と頂点を保つ、正規化した錐空間の制限。 -/
def normalizedConeRestrictionFiber (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneMappingSpace F x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneMappingSpace p x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p)
    (normalizedConeRestriction F i hi) (normalizedConeRestriction_projection F i hi) x

/-- 頂点固定の正規化した制限は、通常の制限と図式の等式による移送の合成。 -/
lemma normalizedConeRestrictionFiber_eq (x : X _⦋0⦌) :
    normalizedConeRestrictionFiber F i hi x = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneRestrictionFiberMap F i x ≫
      eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneMappingSpace a x) hi) := by
  cases hi
  simp only [normalizedConeRestrictionFiber, normalizedConeRestriction,
    eqToHom_refl, Category.comp_id]
  rfl

/-- pushout の共通部分での元の図式の二表示は可換性から厳密に一致。 -/
lemma conePushoutBoundary_eq {B D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {r : B ⟶ D} {s : C ⟶ D} (hp : IsPushout f g r s) (q : D ⟶ X) :
    g ≫ (s ≫ q) = f ≫ (r ≫ q) := by
  rw [← Category.assoc, ← Category.assoc, hp.w]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
