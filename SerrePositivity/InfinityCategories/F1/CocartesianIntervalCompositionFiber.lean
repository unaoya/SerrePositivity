module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalOuterHornPullback
public import SerrePositivity.InfinityCategories.F1.VertexFiberIsPullbackIso
public import SerrePositivity.InfinityCategories.Stable.KanContractibleBaseFiber

/-!
概要：同じ合成三角形を固定した fiber を、元の外ホーン延長と厳密に同定する。
方針：元の pullback の fiber 同型と、可縮な底上の Kan fibration の fiber 同値を使う。
規約：同じ第二三角形への実際の射影を保持する。
使われ方：元の固定成分 Hom fiber を、指定された外ホーンの延長空間と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)
local notation "C₀" => (cocartesianIntervalCompositionSpace F G v)
local notation "p" => (cocartesianIntervalCompositionTriangleMap F G v)
local notation "q" => (cocartesianIntervalOuterHornMap F G v)
local notation "r" => (NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 2))) CatInfinity)

attribute [local instance] vertexFiber_quasicategory_of_innerFibration
attribute [local instance] cocartesianIntervalCompositionTriangleMap_fibration

local instance : KanComplex E := by
  letI := cocartesianHomIntervalEvaluation_fibration F G c
  exact vertexFiber_kanComplex_of_leftFibration _ _

local instance : KanComplex C₀ :=
  (cocartesianIntervalCompositionSpace_isContractibleKan F G v).kanComplex

/-- 同じ合成三角形上の実際の fiber は、同じ外ホーンの延長空間と厳密に同型。 -/
def cocartesianIntervalOuterHornFiberIso (s : C₀ _⦋0⦌) :
    vertexFiber p s ≅ vertexFiber r ((q).app (Opposite.op ⦋0⦌) s) :=
  vertexFiberIsoOfIsPullback (cocartesianIntervalOuterHorn_isPullback F G v) s

/-- 同じ fiber 同型は、元の第二三角形への実際の制限を保持する。 -/
lemma cocartesianIntervalOuterHornFiberIso_hom_ι (s : C₀ _⦋0⦌) :
    (cocartesianIntervalOuterHornFiberIso F G v s).hom ≫
        vertexFiberι r ((q).app (Opposite.op ⦋0⦌) s) =
      vertexFiberι p s ≫ cocartesianIntervalSecondTriangleMap F G v :=
  vertexFiberIsoOfIsPullback_hom_ι (cocartesianIntervalOuterHorn_isPullback F G v) s

/-- 任意の同じ指定合成三角形上の fiber の包含は、元の固定成分 Hom fiber の同値。 -/
lemma cocartesianIntervalCompositionFiber_ι_isQCatEquivalence (s : C₀ _⦋0⦌) :
    IsQCatEquivalence (vertexFiberι p s) :=
  vertexFiberι_isQCatEquivalence_of_contractible_base p
    (cocartesianIntervalCompositionSpace_isContractibleKan F G v) s

/-- 同じ外ホーン延長から、元の実際の固定成分 Hom fiber への指定射。 -/
def cocartesianIntervalOuterHornFiberComparison (s : C₀ _⦋0⦌) :
    vertexFiber r ((q).app (Opposite.op ⦋0⦌) s) ⟶ E :=
  (cocartesianIntervalOuterHornFiberIso F G v s).inv ≫ vertexFiberι p s

/-- 同じ外ホーン延長の指定射は、元の固定成分 Hom fiber の同値。 -/
lemma cocartesianIntervalOuterHornFiberComparison_isQCatEquivalence (s : C₀ _⦋0⦌) :
    IsQCatEquivalence (cocartesianIntervalOuterHornFiberComparison F G v s) := by
  let e := cocartesianIntervalOuterHornFiberIso F G v s
  exact (qCatEquivalenceOfIso e.symm).isQCatEquivalence.comp
    (cocartesianIntervalCompositionFiber_ι_isQCatEquivalence F G v s)

/-- 同じ外ホーン延長の指定射から第二三角形を取り出すと、元の延長そのもの。 -/
lemma cocartesianIntervalOuterHornFiberComparison_second (s : C₀ _⦋0⦌) :
    cocartesianIntervalOuterHornFiberComparison F G v s ≫
      cocartesianIntervalSecondTriangleMap F G v =
    vertexFiberι r ((q).app (Opposite.op ⦋0⦌) s) := by
  unfold cocartesianIntervalOuterHornFiberComparison
  rw [Category.assoc, ← cocartesianIntervalOuterHornFiberIso_hom_ι, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories
