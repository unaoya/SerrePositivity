module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.ConeSectionsValueShapeNaturality

/-!
概要：図式の表示の等式を残した形状制限でも、元の値の切断写像を保つ。
方針：制限の終域だけを指定等式で移し、等式消去で一般の形状自然性に帰着する。
規約：元の錐・頂点を保ち、等式の証明を選び直さない。
使われ方：要素の圏に沿う G8 の実切断制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 同じ小さい実切断の制限を、指定図式の表示へ移した射。 -/
def normalizedSmallSectionsRestriction {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ SpaceInfinity.{u})
    (i : K ⟶ B) (hi : (SSet.uliftFunctor.{u + 1, u}).map i ≫ F = G) :
    (coherentSpaceSectionsObject F).obj ⟶ (coherentSpaceSectionsObject G).obj :=
  smallUnstraighteningSectionsRestriction F i ≫
    eqToHom (congrArg (fun H ↦ (coherentSpaceSectionsObject H).obj) hi)

/-- 指定表示へ移した制限も、元の錐の値からの切断写像を全族で保つ。 -/
def coneSectionsValueMapAt_normalizedShapeIso {B K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ SpaceInfinity.{u})
    (i : K ⟶ B) (hi : (SSet.uliftFunctor.{u + 1, u}).map i ≫ F = G)
    (c : JoinCone F) (d : JoinCone G)
    (hd : d.val = joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
      ((SSet.uliftFunctor.{u + 1, u}).map i) ≫ c.val)
    (z : SpaceInfinity.{u} _⦋0⦌) (hc : c.vertex = z) (hz : d.vertex = z) :
    FunctorIso
      (coneSectionsValueMapAt F c z hc ≫
        (SSet.uliftFunctor.{u + 1, u}).map (normalizedSmallSectionsRestriction F G i hi))
      (coneSectionsValueMapAt G d z hz) := by
  subst G
  simpa only [normalizedSmallSectionsRestriction, eqToHom_refl, Category.comp_id] using
    coneSectionsValueMapAt_shapeIso F i c d hd z hc hz

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
