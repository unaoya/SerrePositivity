module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBousfieldKanSetCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomSpace
/-!
概要：同じMoore反転の指定鎖ホモトピー同値を非有界BK Homへ移す。
方針：既存の反変endのホモトピー移送と指定符号付きend–Hom同型を使う。
規約：IS-W2 A12の証明分割。順射は元のMoore反転の像を保持する。
使われ方：HA 1.2.4、反転重み上の指定Γ比較への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicTopology CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]
/-- 元のBK重みを反転して正規化した同じ係数鎖複体。 -/
def reflectedNormalizedBKWeight : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A) ℕ :=
  (normalizedMooreComplex _).obj
    (SimplicialObject.opFunctor.obj (linearizedSimplicialWeight A bousfieldKanSetWeight))
/-- 同じ反転正規化重みから元の係数図式への線形Hom。 -/
def reflectedNormalizedBKHom (X : CosimplicialObject (Complex A)) : Complex A :=
  linearHomComplex A (reflectedNormalizedBKWeight.extend ComplexShape.embeddingDownNat)
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram X))
/-- 指定Moore反転を反変endと同じ符号付き同型で運ぶ鎖ホモトピー同値。 -/
def normalizedBKReverseHomotopyEquiv (X : CosimplicialObject (Complex A)) :
    HomotopyEquiv (normalizedBousfieldKanHom X) (reflectedNormalizedBKHom X) := by
  let W := linearizedSimplicialWeight A bousfieldKanSetWeight
  exact (HomotopyEquiv.ofIso (weightEndHomIso A _ (doubleOppositeDiagram X)).symm).trans
    ((linearWeightEndTotalHomotopyEquiv A (doubleOppositeDiagram X)
      (normalizedMooreReverseHomotopyEquiv W)).trans
        (HomotopyEquiv.ofIso (weightEndHomIso A _ (doubleOppositeDiagram X))))
/-- 上の指定順射の同じΓ像。 -/
def normalizedBKReverseSpaceMap (X : CosimplicialObject (Complex A)) :
    (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X) :=
  (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (normalizedBKReverseHomotopyEquiv X).hom
/-- 同じ反転比較のΓ像自身が単体的ホモトピー同値。 -/
theorem normalizedBKReverseSpaceMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKReverseSpaceMap X) := by
  have : QuasiIso (normalizedBKReverseHomotopyEquiv X).hom := inferInstance
  exact truncatedDoldKanFunctor_quasiIso_equivalence (normalizedBKReverseHomotopyEquiv X).hom
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
