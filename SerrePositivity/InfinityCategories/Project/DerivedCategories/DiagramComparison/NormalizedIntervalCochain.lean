module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalRawChain
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedChainsHom
/-!
概要：二つの閉零次値とその境界を持つ同じ正規化区間の評価。
方針：smart切断への鎖写像を、既存の零延長・切断の随伴で戻す。
規約：A06の証明の分割。元の正規化区間と負次数埋め込みを保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 境界の式から構成した同じ正規化コチェイン区間の写像。 -/
def normalizedIntervalCochainMap (A : Type u) [CommRing A]
    (H : CochainComplex (ModuleCat.{u} A) ℤ)
    (x y : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0)
    (w : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1)
    (hw : (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ H :=
  (SerrePositivity.EInfinity.ComplexLimits.normalizedChainsTruncationHomEquiv A
    (SSet.stdSimplex.obj ⦋1⦌) H).symm
    (intervalNormalizedChainMap A (H.truncLE' (ComplexShape.embeddingUpIntLE 0)) x y w hw)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
