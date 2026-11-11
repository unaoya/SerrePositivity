module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSquare
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalityTriangles

/-!
概要：元の豊穣 Hom の二つの族を、同じ二辺を持つ合成三角形へ写す。
方針：検証済みの coherent 合成四角形を零番三角形へ制限する。
規約：二つの Hom の全パラメーターを保つ。
使われ方：標準 Hom 比較から合成三角形全体への実際の比較を作る。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C)

/-- 二つの元の Hom の全体をパラメーターとする、同じ coherent 合成三角形。 -/
def coherentCompositionTriangle :
    Δ[2] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) ⟶ SimplicialNerve C :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSquare X Y Z) 0

/-- 同じ合成三角形の第一辺は、元の第一 Hom の標準比較そのもの。 -/
lemma coherentCompositionTriangle_first :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ coherentCompositionTriangle X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) := by
  rw [coherentCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle_zero_initial,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSquare_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  rfl

/-- 同じ合成三角形の第二辺は、元の第二 Hom の標準比較そのもの。 -/
lemma coherentCompositionTriangle_last :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ coherentCompositionTriangle X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) := by
  rw [coherentCompositionTriangle, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.squarePrismTriangle_zero_final,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSquare_inner_one]
  rfl

/-- 三角形の族の第一辺の式は、任意の同時パラメーター制限でも保持される。 -/
lemma coherentCompositionTriangle_first_precomp {T : SSet.{max u v}}
    (a : T ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) :
    (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ (Δ[2] ◁ a) ≫
        coherentCompositionTriangle X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    coherentCompositionTriangle_first, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

/-- 三角形の族の第二辺の式も、任意の同時パラメーター制限で保持される。 -/
lemma coherentCompositionTriangle_last_precomp {T : SSet.{max u v}}
    (a : T ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ (Δ[2] ◁ a) ≫
        coherentCompositionTriangle X Y Z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (a ≫ snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    coherentCompositionTriangle_last, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
