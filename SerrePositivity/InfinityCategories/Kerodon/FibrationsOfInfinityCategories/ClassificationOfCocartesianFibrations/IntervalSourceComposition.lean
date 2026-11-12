module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalCompositionTriangle

/-!
概要：実際の source の固定成分から、指定すべき同じ合成三角形を構成する。
方針：成分頂点を元の通常の射に戻し、始域の輸送との strict な合成三角形を使う。
規約：標準 Hom 比較が指定する実際の頂点と辺を保持する。
使われ方：元の第一三角形を固定した fiber への比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1)
local notation "D" => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "v" => (NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison B D) (Opposite.op ⦋0⦌) b)
local notation "f₀₁" => (CategoryTheory.Functor.map F.val _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow : A ⟶ B)
local notation "k" => (Equiv.symm (SimplicialCategory.homEquiv' B D) b.down)

/-- 同じ固定成分の通常の射と始域の輸送との、指定された strict 合成三角形。 -/
def cocartesianIntervalSourceCompStruct :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (X := A) (Y := D) (f₀₁ ≫ k)) :=
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (X := A) (Y := B) (Z := D) f₀₁ k
  SSet.Edge.CompStruct.mk s.simplex s.d₂
    (s.d₀.trans
      (congrArg SSet.Edge.edge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison_vertex_edge (X := B) (Y := D) b.down)).symm)
    s.d₁

/-- 元の source の固定成分から指定した、実際の比較先の合成空間の頂点。 -/
def cocartesianIntervalSourceCompositionVertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleVertexOfCompStruct (cocartesianIntervalSourceCompStruct F G b)

/-- 指定合成頂点の全パラメーターの族は、元の strict な合成三角形そのもの。 -/
lemma cocartesianIntervalSourceCompositionVertex_uncurry {T : SSet.{u + 1}} :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u})
        (a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge F)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v))
        (SSet.const (cocartesianIntervalSourceCompositionVertex F G b) :
          T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v) =
      fst (Δ[2] : SSet.{u + 1}) T ≫
        SSet.yonedaEquiv.symm (cocartesianIntervalSourceCompStruct F G b).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleVertexOfCompStruct_uncurry (T := T)
    (cocartesianIntervalSourceCompStruct F G b)

/-- 同じ指定三角形の対角は、固定成分と元の輸送射の通常の合成に定値。 -/
lemma cocartesianIntervalSourceCompositionVertex_diagonal {T : SSet.{u + 1}} :
    (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u})
          (a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.composableEdgeHorn (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge F)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v))
          (SSet.const (cocartesianIntervalSourceCompositionVertex F G b) :
            T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v) =
      fst (Δ[1] : SSet.{u + 1}) T ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (X := A) (Y := D) (f₀₁ ≫ k)).edge := by
  rw [cocartesianIntervalSourceCompositionVertex_uncurry, ← Category.assoc,
    whiskerRight_fst, Category.assoc]
  exact congrArg (fun h ↦ fst (Δ[1] : SSet.{u + 1}) T ≫ h)
    (cocartesianIntervalSourceCompStruct F G b).δ_one_yonedaEquiv_symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
