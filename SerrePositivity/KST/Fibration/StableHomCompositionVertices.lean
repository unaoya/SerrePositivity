module
public import SerrePositivity.KST.Fibration.ZeroStableHomTransport
public import SerrePositivity.KST.Fibration.CoherentSimplexHomVertices
public import SerrePositivity.KST.SConstruction.SExactCoreEnrichedFunctor

/-! # 元の完全関手の合成頂点と、零圏を経由する全 Hom の零値判定 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の通常完全射の全 Hom の頂点表示は、同じ元の関手頂点を回収する。 -/
theorem stableHomAmbient_homEquiv' {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : A ⟶ B) :
    (stableHomAmbient A B).app (Opposite.op ⦋0⦌)
      (SimplicialCategory.homEquiv' A B f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f.hom := by
  have he := (congrArg (fun h => h ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι)
    (stableExactCoreHomEquiv_inclusion f)).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι f)
  exact congrArg (SSet.unitHomEquiv _)
    ((Category.assoc (eHomEquiv SSet f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι).symm.trans he)

/-- 零圏を通る元の二つの完全関手の全 Hom の合成頂点は零値関手である。 -/
theorem stableHomZeroVertex_comp_throughZero {A Z B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory Z) (v : (A ⟶[SSet.{u}] Z) _⦋0⦌)
    (w : (Z ⟶[SSet.{u}] B) _⦋0⦌) :
    StableHomZeroVertex A B ((eComp SSet A Z B).app (Opposite.op ⦋0⦌) (v, w)) := by
  obtain ⟨f, rfl⟩ := (SimplicialCategory.homEquiv' A Z).surjective v
  obtain ⟨g, rfl⟩ := (SimplicialCategory.homEquiv' Z B).surjective w
  have hz : StableHomZeroVertex A B (SimplicialCategory.homEquiv' A B (f ≫ g)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableHomAmbient A B).app (Opposite.op ⦋0⦌) _)
    have hf := isZeroVertex_functorVertex_of_pointwise (f.hom ≫ g.hom)
      (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := g.hom) _
        (hZ (f.hom.app (Opposite.op ⦋0⦌) a)))
    exact (stableHomAmbient_homEquiv' (f ≫ g)).symm ▸ hf
  exact simplicialHomVertex_comp f g ▸ hz

end SerrePositivity.KST.Fibration
