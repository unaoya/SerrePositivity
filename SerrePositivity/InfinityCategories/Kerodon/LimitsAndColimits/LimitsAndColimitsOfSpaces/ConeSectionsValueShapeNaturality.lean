module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallSectionsShapeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsMapShapeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsValueMap

/-!
概要：元の錐の値からの切断写像は、小さい実切断の形状制限と全族で可換。
方針：元の大きい全 fiber の比較に、同じ値同値の逆と切断表示同型を合成する。
規約：大小の切断を同一視せず、指定された比較同型を通す。
使われ方：G8 の指定極限比較の形状自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 小さい切断表示の逆も、実際の形状制限と厳密に可換。 -/
lemma smallUnstraighteningSectionsIso_inv_shape {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B) :
    (smallUnstraighteningSectionsIso F).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningSectionsRestriction F i) =
    unstraighteningSectionsRestriction F ((SSet.uliftFunctor.{u + 1, u}).map i) ≫
      (smallUnstraighteningSectionsIso ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)).inv := by
  apply (cancel_mono (smallUnstraighteningSectionsIso
    ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [smallUnstraighteningSectionsIso_shape, Iso.inv_hom_id_assoc]

/-- 元の錐の値の全切断写像は、同じ形状の小さい実切断制限と全族で可換。 -/
def coneSectionsValueMapAt_shapeIso {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (i : K ⟶ B)
    (c : JoinCone F) (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F))
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      ((SSet.uliftFunctor.{u + 1, u}).map i) ≫ c.val)
    (z : SpaceInfinity.{u} _⦋0⦌) (hc : c.vertex = z) (hz : d.vertex = z) :
    FunctorIso
      (coneSectionsValueMapAt F c z hc ≫
        (SSet.uliftFunctor.{u + 1, u}).map (smallUnstraighteningSectionsRestriction F i))
      (coneSectionsValueMapAt _ d z hz) := by
  have h := FunctorIso.postcomp
    (FunctorIso.precomp (coneSectionsMapAt_shapeIso F
      ((SSet.uliftFunctor.{u + 1, u}).map i) c d hd z hc hz)
        (pointedSpaceFiberValueEquivalence z).symm.hom)
    (smallUnstraighteningSectionsIso ((SSet.uliftFunctor.{u + 1, u}).map i ≫ F)).inv
  simpa only [coneSectionsValueMapAt, Category.assoc,
    smallUnstraighteningSectionsIso_inv_shape] using h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
