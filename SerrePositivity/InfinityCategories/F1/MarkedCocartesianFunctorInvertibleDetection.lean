module

public import SerrePositivity.InfinityCategories.F1.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionInvertibleDetection
public import SerrePositivity.InfinityCategories.F1.PreFiberKan

/-!
概要：指定辺を保つ相対 Hom の辺の可逆性を元の全空間の成分で検出する。
方針：全部分複体と相対 fiber の包含で可逆性を反映し、各頂点で評価する。
規約：可逆性は指定辺だけでなく始域の全頂点で検査する。
使われ方：元の cocartesian Hom の core の所属の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺を保つ元の相対関手を、一つの始域の頂点で評価する。 -/
def markedCocartesianFunctorEvaluate {A E B : SSet.{u}} (q : E ⟶ B) (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) (x : A _⦋0⦌) : markedCocartesianFunctorSpace q a W ⟶ E :=
  markedCocartesianFunctorInclusion q a W ≫
    vertexFiberι ((ihom A).map q) (functorVertex a) ≫ evaluateFunctorAt x

/-- 元の指定辺を保つ相対 Hom の辺は、全ての成分で可逆なとき、かつそのときに限り可逆。 -/
lemma isInvertibleEdge_markedCocartesianFunctor_iff_evaluate {A E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [InnerFibration q] (a : A ⟶ B) (W : Set (A _⦋1⦌))
    {v w : (markedCocartesianFunctorSpace q a W) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (markedCocartesianFunctorSpace q a W)) v w) :
    IsInvertibleEdge e ↔ ∀ x : A _⦋0⦌, IsInvertibleEdge
      (e.map ((truncation 2).map (markedCocartesianFunctorEvaluate q a W x))) := by
  let : Quasicategory E := quasicategory_of_innerFibration q
  constructor
  · intro he x
    exact he.map _
  · intro he
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι
      (relativeFunctorSpace q a) (markedCocartesianFunctorPredicate q a
        W)).reflects_isInvertibleEdge e
    apply (isInvertibleEdge_vertexFiber_iff ((ihom A).map q) (functorVertex a) _).mpr
    apply (isInvertibleEdge_internalHom_iff_evaluate _).mpr
    exact he

/-- 指定辺を保つ前合成と、元の関手の頂点での評価は厳密に可換。 -/
lemma markedCocartesianFunctorEvaluate_overPre {E B : SSet.{u}} (q : E ⟶ B)
    {a b : Over B} (i : a ⟶ b) (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) (x : a.left _⦋0⦌) :
    markedCocartesianFunctorPre q i V W hi ≫ markedCocartesianFunctorEvaluate q a.hom V x =
      markedCocartesianFunctorEvaluate q b.hom W (i.left.app (Opposite.op ⦋0⦌) x) := by
  unfold markedCocartesianFunctorEvaluate
  rw [← Category.assoc, markedCocartesianFunctorPre_ι, Category.assoc,
    ← Category.assoc (relativeFunctorOverPre q i),
    relativeFunctorOverPre_ι, Category.assoc, evaluateFunctorAt_pre]

end SerrePositivity.InfinityCategories
