module

public import SerrePositivity.InfinityCategories.F1.CocartesianRelativeRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.CocartesianPredicateIso
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianSectionsPrecomposition

/-!
概要：cocartesian section の単射による制限は、単射な同値を右に持ち上げる。
方針：全ての辺の cocartesian 性の同型不変性を証明し、全部分複体への制限定理を使う。
規約：制限する単射の同値性を仮定せず、元の cocartesian fibration だけを用いる。
使われ方：高次の section の境界固定の貼り合わせと Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全辺を cocartesian に送る section の頂点条件は、元の相対関手空間の同型で不変。 -/
lemma kanIsCocartesianSection_iff_of_vertexIso {A E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] (a : A ⟶ B)
    {v w : (relativeFunctorSpace p a) _⦋0⦌} (h : VertexIso v w) :
    KanIsCocartesianSection p a v ↔ KanIsCocartesianSection p a w := by
  let : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨f, hf, rfl⟩ := exists_relativeFunctorVertex p a v
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex p a w
  simp only [KanIsCocartesianSection]
  have hi := relativeFunctorVertex_functorIso p a hf hg h
  exact forall_congr' (fun e ↦ isCocartesianEdge_iff_of_functorIso p hi e)

/-- 単射による元の section の制限は、単射な前合成同値の全相対持ち上げを持つ。 -/
lemma kanEquivalenceLifting_kanCocartesianSectionsPre
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    F1B.KanEquivalenceLifting (kanCocartesianSectionsPre p i) := by
  let : Quasicategory (SerrePositivity.InfinityCategories.relativeFunctorSpace p b.hom) :=
    inferInstanceAs (Quasicategory (relativeFunctorSpace p b.hom))
  intro K L j hj he
  exact kanEquivalenceLifting_fullRestriction
    (KanIsCocartesianSection p b.hom)
    (fun h ↦ kanIsCocartesianSection_iff_of_vertexIso p b.hom h)
    (KanIsCocartesianSection p a.hom) (kanCocartesianSectionsPre p i)
    (relativeFunctorOverPre p i) (kanCocartesianSectionsPre_ι p i)
    (kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian p i) j hj he

/-- 元の section の単射による制限は inner fibration。 -/
lemma innerFibration_kanCocartesianSectionsPre
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    InnerFibration (kanCocartesianSectionsPre p i) :=
  F1B.KanEquivalenceLifting.innerFibration
    (U := kanCocartesianSectionsPre p i) (kanEquivalenceLifting_kanCocartesianSectionsPre p i)

end SerrePositivity.InfinityCategories
