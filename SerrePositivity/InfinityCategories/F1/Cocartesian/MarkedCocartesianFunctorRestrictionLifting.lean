module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.MarkedCocartesianFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PredicateIso
public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeRestrictionLifting
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoreIsofibration

/-!
概要：指定辺を保つ相対 Hom の単射による制限の同値持ち上げと core の Kan 充填性。
方針：指定辺の保存条件の同型不変性で、元の全相対 Hom の持ち上げを制限する。
規約：始域の辺の指定は任意で、制限する単射の同値性を要求しない。
使われ方：各底変換上の元の Hom の core のセルによる貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定辺の cocartesian 性は、同じ相対関手空間の頂点の同型で不変。 -/
lemma markedCocartesianFunctorPredicate_iff_of_vertexIso {A E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [InnerFibration q] (a : A ⟶ B)
    (W : Set (A _⦋1⦌)) {v w : (relativeFunctorSpace q a) _⦋0⦌} (h : VertexIso v w) :
    markedCocartesianFunctorPredicate q a W v ↔ markedCocartesianFunctorPredicate q a W w := by
  let : Quasicategory E := quasicategory_of_innerFibration q
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex q a v
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex q a w
  rw [markedCocartesianFunctorPredicate_vertex, markedCocartesianFunctorPredicate_vertex]
  exact forall_congr' (fun e ↦ imp_congr_right (fun _ ↦
    isCocartesianEdge_iff_of_functorIso q (relativeFunctorVertex_functorIso q a hf hg h) e))

/-- 指定辺を保つ Hom の単射による制限は、単射な前合成同値の相対持ち上げを持つ。 -/
lemma kanEquivalenceLifting_markedCocartesianFunctorPre {E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left]
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (markedCocartesianFunctorPre q i V W hi) := by
  intro K L j hj he
  exact kanEquivalenceLifting_fullRestriction (markedCocartesianFunctorPredicate q b.hom W)
    (fun h ↦ markedCocartesianFunctorPredicate_iff_of_vertexIso q b.hom W h)
    (markedCocartesianFunctorPredicate q a.hom V) (markedCocartesianFunctorPre q i V W hi)
    (relativeFunctorOverPre q i) (markedCocartesianFunctorPre_ι q i V W hi)
    (kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian q i) j hj he

/-- 同じ指定辺を保つ Hom の core の単射による制限は Kan fibration。 -/
lemma core_markedCocartesianFunctorPre_fibration {E B : SSet.{u}}
    [Quasicategory B] (q : E ⟶ B) [CocartesianFibration q]
    {a b : Over B} (i : a ⟶ b) [Mono i.left]
    (V : Set (a.left _⦋1⦌)) (W : Set (b.left _⦋1⦌))
    (hi : ∀ e ∈ V, i.left.app (Opposite.op ⦋1⦌) e ∈ W) :
    Fibration (quasicategoryCoreMap (markedCocartesianFunctorPre q i V W hi)) :=
  F2.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_markedCocartesianFunctorPre q i V W hi)

end SerrePositivity.InfinityCategories
