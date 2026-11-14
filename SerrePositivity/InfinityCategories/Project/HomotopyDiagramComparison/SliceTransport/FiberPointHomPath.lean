module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PointHomActionComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PointHomTransportPath
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：同じ底の fiber 内の指定辺に沿い、既存の点 Hom の全パラメータ族を比較する。
方針：両端の点の族を同じ全始点の作用と比較し、指定辺の同じ像と合成する。
規約：辺の類は保持し、裸のホモトピー存在命題から代表を選ばない。
使われ方：左右の実際の輸送余錐を結ぶ指定経路に沿う全 Hom 係数の変化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a b : B _⦋0⦌)

/-- 同じ指定始点の Hom を、fiber の実際の点の底による表示へ移す同型。 -/
def fiberPointHomParameterIso (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (p.app (Opposite.op ⦋0⦌) v.val) b :=
  eqToIso (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft z b)
    (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)).symm)

/-- 指定した同じ底の Hom 上で表示した、既存の点 Hom の族。 -/
def fiberPointHomFamily (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b :=
  (fiberPointHomParameterIso p a b v).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationPointHomFamily p v.val b

/-- 既存の点の族と全始点の作用を、同じ指定底の Hom 上で比較する実際の円柱。 -/
def fiberPointHomActionComparison (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) :
    SSet.Homotopy (fiberPointHomFamily p a b v) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportActionAt p a b v) := by
  rcases v with ⟨d, hd⟩
  have h : p.app (Opposite.op ⦋0⦌) d = a := hd.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  subst a
  simpa only [fiberPointHomFamily, fiberPointHomParameterIso, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomSourceVertex, eqToIso_refl,
    Iso.refl_hom, Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomActionComparisonHomotopy p d b

variable {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌} (k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a).Edge v w)

/-- 指定辺を全 Hom の族で写した同型。両端の実際の比較と同じ辺の作用から作る。 -/
def fiberPointHomPathIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fiberPointHomFamily p a b v) (fiberPointHomFamily p a b w) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (fiberPointHomActionComparison p a b v) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointHomTransportPathHomotopy p a b k) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (fiberPointHomActionComparison p a b w)).symm

/-- 指定した同じ fiber 辺に沿う、元の点 Hom の全パラメータ族のホモトピー。 -/
def fiberPointHomPathHomotopy :
    SSet.Homotopy (fiberPointHomFamily p a b v) (fiberPointHomFamily p a b w) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  exact (fiberPointHomPathIso p a b k).simplicialHomotopy

/-- 選んだ円柱の辺の類は、指定辺の作用と両端の実際の比較の合成を厳密に保つ。 -/
lemma fiberPointHomPathHomotopy_hom :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (fiberPointHomPathHomotopy p a b k)) =
      (fiberPointHomPathIso p a b k).hom := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIso_simplicialHomotopy_hom _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
