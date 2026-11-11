module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCosliceComparison

/-!
概要：表現可能な weighted 係数を豊穣関手で写す自然変換。
方針：豊穣合成の保存を全単体で評価し、通常の射の定値係数を照合する。
規約：局所 Kan 性を要求せず、全係数単体の作用を保持する。
使われ方：weighted coslice 比較と実際の coherent nerve の後合成の可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 通常の射の豊穣単位からの像は、全次数で同じ Hom 頂点の定値単体。 -/
lemma enrichedHomEquiv_app_constant {x y : C} (f : x ⟶ y) (n : ℕ) :
    (eHomEquiv SSet f).app (Opposite.op ⦋n⦌) PUnit.unit =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' x y f) n := by
  exact (congrArg (fun k => k.app (Opposite.op ⦋n⦌) PUnit.unit)
    ((SSet.unitHomEquiv _).symm_apply_apply (eHomEquiv SSet f))).symm

/-- 豊穣関手の全 Hom の作用は、通常の射による表現可能な係数の後合成と可換。 -/
lemma enrichedHomMap_whiskerLeft (R : EnrichedFunctor SSet.{u} C D)
    (x : C) {y z : C} (f : y ⟶ z) :
    (((SimplicialCategory.sHomFunctor C).obj (Opposite.op x)).map f) ≫ R.map x z =
      R.map x y ≫ (((SimplicialCategory.sHomFunctor D).obj (Opposite.op (R.obj x))).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have h := congrArg (fun k => k.app (Opposite.op ⦋n⦌)
    (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' y z f) n)) (R.map_comp x y z)
  change (R.map x z).app (Opposite.op ⦋n⦌)
    ((eComp SSet x y z).app _
      (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' y z f) n)) =
    (eComp SSet (R.obj x) (R.obj y) (R.obj z)).app _
      ((R.map x y).app _ s,
        (R.map y z).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' y z f) n)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex] at h
  change (R.map x z).app (Opposite.op ⦋n⦌)
    ((eComp SSet x y z).app _ (s, (eHomEquiv SSet f).app _ PUnit.unit)) =
    (eComp SSet (R.obj x) (R.obj y) (R.obj z)).app _
      ((R.map x y).app _ s,
        (eHomEquiv SSet ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f)).app _ PUnit.unit)
  rw [enrichedHomEquiv_app_constant, enrichedHomEquiv_app_constant]
  exact h

/-- 表現可能な係数図式は、全 Hom の作用そのもので豊穣関手の像の係数図式へ写る。 -/
def weightedHomFunctorImage {I : Type u} [SmallCategory I]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C D) (x : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) (R.obj x) where
  app i := R.map x (F.obj i)
  naturality _i _j f := enrichedHomMap_whiskerLeft R x (F.map f)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
