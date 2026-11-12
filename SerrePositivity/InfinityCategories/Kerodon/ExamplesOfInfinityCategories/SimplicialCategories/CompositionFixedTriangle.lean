module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFaces

/-!
概要：第二射を固定した元の豊穣 Hom 全体の合成三角形を構成する。
方針：二つの Hom を動かす三角形の第二パラメーターを元の射の頂点に固定する。
規約：第一辺は標準 Hom 比較、第二辺は同じ coherent な射に厳密に一致する。
使われ方：合成三角形全体への比較と後合成の fiber の比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C) (f : Y ⟶ Z)

/-- 元の第一 Hom の各単体に、同じ第二射の定値単体を組み合わせる。 -/
def coherentCompositionFixedParameter :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z) :=
  lift (𝟙 _) (SSet.const (ULift.up (SimplicialCategory.homEquiv' Y Z f)))

/-- 第二射を固定した、元の第一 Hom の全体を動かす合成三角形。 -/
def coherentCompositionFixedTriangle :
    Δ[2] ⊗ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⟶ SimplicialNerve C :=
  (Δ[2] ◁ coherentCompositionFixedParameter X Y Z f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle X Y Z

/-- 同じ三角形の第一辺は、元の第一 Hom の標準比較そのもの。 -/
lemma coherentCompositionFixedTriangle_first :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ coherentCompositionFixedTriangle X Y Z f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) := by
  rw [coherentCompositionFixedTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_first_precomp,
    ← Category.assoc]
  simp only [coherentCompositionFixedParameter, lift_fst, Category.id_comp]

/-- 同じ三角形の第二辺は、元の第二射の coherent な辺に厳密に定値。 -/
lemma coherentCompositionFixedTriangle_last :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ coherentCompositionFixedTriangle X Y Z f =
      fst (Δ[1] : SSet.{max u v}) _ ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  rw [coherentCompositionFixedTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionTriangle_last_precomp,
    ← Category.assoc, coherentCompositionFixedParameter, lift_snd,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  congr 2

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
