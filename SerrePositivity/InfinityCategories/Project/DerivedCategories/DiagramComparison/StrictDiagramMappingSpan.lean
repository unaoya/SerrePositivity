module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramCofibrantVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramEvaluationFactorization
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
概要：元の局所化の任意二頂点に対し、実frameを源とする全写像空間のspanを作る。
方針：同じcofibrant表示のright frameを使い、元の局所化の端点同型を通して評価する。
規約：右脚の同値性は別の主張。比較の同値性を入力にしてspanを作らない。
使われ方：HTT 4.2.4.4の加群版の指定実評価の充満忠実性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet MonoidalClosed
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance isw1StrictDiagramMappingSpanLocal1 : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance isw1StrictDiagramMappingSpanLocal2 : CategoryTheory.Limits.HasInitial (StrictComplexDiagram A d) :=
  (CategoryTheory.Limits.isZero_zero (StrictComplexDiagram A d)).isInitial.hasInitial
local instance isw1StrictDiagramMappingSpanLocal3 (x : (StrictDiagramInfinity A d) _⦋0⦌) :
    IsCofibrant (strictDiagramCofibrantVertex A d x) :=
  strictDiagramCofibrantVertex_isCofibrant A d x
local instance isw1StrictDiagramMappingSpanLocal4 (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    SSet.KanComplex ((strictDiagramRightFrameMapping A d
      (strictDiagramCofibrantVertex A d x)).obj (strictDiagramCofibrantVertex A d y)) :=
  rightFrameHom_kanComplex (strictDiagramRightFrameFamily A d) _ _

/-- 任意二頂点を同じcofibrant図式で表示して取る、元の実right frame Hom。 -/
abbrev strictDiagramMappingSpace (x y : (StrictDiagramInfinity A d) _⦋0⦌) : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj
    ((strictDiagramRightFrameMapping A d (strictDiagramCofibrantVertex A d x)).obj
      (strictDiagramCofibrantVertex A d y))

/-- 同じ実frameから、元の指定局所化の同じ任意二端点の写像空間への全同値。 -/
def strictDiagramMappingSpaceEquivalence (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    QCatEquivalence (strictDiagramMappingSpace A d x y)
      (pinchedHom (X := StrictDiagramInfinity A d) x y) :=
  (strictDiagramRightFramePinchedEquivalence A d
    (strictDiagramCofibrantVertex A d x) (strictDiagramCofibrantVertex A d y)).trans
      (pinchedEndpointEquivalence (strictDiagramCofibrantVertexIso A d x)
        (strictDiagramCofibrantVertexIso A d y))

/-- spanの左脚。同じ実frameと同じ端点同型から作る。 -/
def strictDiagramMappingLeft (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    strictDiagramMappingSpace A d x y ⟶ pinchedHom (X := StrictDiagramInfinity A d) x y :=
  (strictDiagramMappingSpaceEquivalence A d x y).hom

/-- spanの右脚。元の指定実評価そのものの写像空間への作用を使う。 -/
def strictDiagramMappingRight (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    strictDiagramMappingSpace A d x y ⟶
      pinchedHom
        ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) x)
        ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) y) :=
  strictDiagramMappingLeft A d x y ≫ pinchedHomMap (strictDiagramDerivedEvaluation A d) x y

/-- 実解像から元の局所化とcoherent図式の全変換空間へ写る同じspan。 -/
def strictDiagramMappingSpan (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    Σ M : SSet.{u + 1}, (M ⟶ pinchedHom (X := StrictDiagramInfinity A d) x y) ×
      (M ⟶ pinchedHom
        ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) x)
        ((strictDiagramDerivedEvaluation A d).app (Opposite.op ⦋0⦌) y)) :=
  ⟨strictDiagramMappingSpace A d x y,
    strictDiagramMappingLeft A d x y, strictDiagramMappingRight A d x y⟩

/-- 同じspanの左脚は、全写像空間の単体的ホモトピー同値。 -/
lemma strictDiagramMappingSpan_left (x y : (StrictDiagramInfinity A d) _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (strictDiagramMappingSpan A d x y).2.1 :=
  (strictDiagramMappingSpaceEquivalence A d x y).isQCatEquivalence.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
