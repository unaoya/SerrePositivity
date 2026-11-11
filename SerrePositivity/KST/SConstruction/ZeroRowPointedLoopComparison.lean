module
public import SerrePositivity.KST.SConstruction.ZeroRowLoopComparison
public import SerrePositivity.KST.SConstruction.ZeroRowPointedFiberComparison
public import SerrePositivity.KST.SConstruction.PointedKanStrictExtension

/-! # 元の点つき零行とその Kan 模型からの具体的な loop 比較
概要：零段の任意の頂点の退化を基点にし、元の loop 射を点つきにして既存の Kan 単位へ延長する。
方針：退化像の定数 loop への厳密な式と、点つき Kan 標的への厳密な延長を使う。
規約：延長は元の射を Kan 単位に沿って厳密に回収する。使われ方：元の構造射の随伴の π_* 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- 元の零段の任意の頂点の退化を基点にした零行からの具体的な点つき loop 射。 -/
def zeroRowPointedLoopComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    zeroRowPointedModel r X b ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X) :=
  Under.homMk (zeroRowLoopComparison r X) (by
    change SSet.const _ ≫ zeroRowLoopComparison r X = _
    rw [← SSet.const_comp b ((iteratedSRealizationDiagram r X).map
      (SimplexCategory.σ (0 : Fin 1)).op), Category.assoc,
      zeroRowLoopComparison_degeneracy, ← Category.assoc, comp_toUnit]
    rfl)

/-- 元の点つき零行の Kan 模型から、既存の loop 空間への厳密な延長。 -/
def zeroRowKanLoopComparison (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedKanReplacement.obj (zeroRowPointedModel r X b) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X) :=
  pointedKanStrictExtension (zeroRowPointedLoopComparison r X b)

/-- 延長した点つき loop 射は元の Kan 単位上で元の零行の射を厳密に回収する。 -/
lemma zeroRowKanLoopComparison_unit (r : ℕ) (X : StableModel.{u})
    (b : ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) _⦋0⦌) :
    PointedKanReplacement.unit.app (zeroRowPointedModel r X b) ≫
      zeroRowKanLoopComparison r X b = zeroRowPointedLoopComparison r X b :=
  pointedKanStrictExtension_fac _

end SerrePositivity.KST.SConstruction
