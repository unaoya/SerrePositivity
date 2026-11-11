module
public import SerrePositivity.KST.Fibration.RelativeDiagramCore
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom

/-! # 関手圏の core と全成分での判定

実自然変換の可逆性の点ごとの判定を、任意次数の core 単体に拡張する。
その結果、商で成分ごとに弱同値となる図式は、実関手圏の core の逆像に一致する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 関手圏の core の全高次単体は、全頂点評価の core 所属で判定できる。 -/
lemma functorCore_mem_iff {K C : SSet.{u}} [Quasicategory C]
    {n : SimplexCategoryᵒᵖ} (s : ((ihom K).obj C).obj n) :
    s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).obj n ↔
      ∀ k : K _⦋0⦌,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app n s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n := by
  change (∀ α : ⦋1⦌ ⟶ n.unop,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((ihom K).obj C).map α.op s))) ↔ _
  constructor
  · intro hs k α
    have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((ihom K).obj C).map α.op s))).1 (hs α) k
    rw [← NatTrans.naturality_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((ihom K).obj C).map α.op s)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app _
        (((ihom K).obj C).map α.op s))) rfl).mp hi
  · intro hs α
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((ihom K).obj C).map α.op s))).2
    intro k
    have hi := hs k α
    rw [← NatTrans.naturality_apply] at hi
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (((ihom K).obj C).map α.op s)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)))
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app _
        (((ihom K).obj C).map α.op s))) rfl).mpr hi

/-- 全評価を持つ実図式の相対条件は、商への後合成による core の逆像である。 -/
lemma relativeDiagram_eq_functorCore_preimage
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B) :
    relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).preimage (d ≫ (ihom K).map q) := by
  ext n s
  exact (functorCore_mem_iff ((d ≫ (ihom K).map q).app n s)).symm

/-- 成分ごとの相対図式は、商の実関手圏の core に写る。 -/
def relativeDiagramFunctorCoreMap
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B) :
    (relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C) : SSet.{u}) :=
  Subcomplex.lift ((relativeDiagram q (fun k => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).ι ≫
    d ≫ (ihom K).map q) (by
    rintro n _ ⟨s, rfl⟩
    exact (functorCore_mem_iff _).2 s.property)

/-- 商の図式への射は、元の実図式と後合成を厳密に保持する。 -/
lemma relativeDiagramFunctorCoreMap_ι
    {K B C X : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (d : X ⟶ (ihom K).obj B) :
    relativeDiagramFunctorCoreMap q d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).ι =
      (relativeDiagram q (fun k : K _⦋0⦌ => d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).ι ≫
        d ≫ (ihom K).map q := rfl

end SerrePositivity.KST.Fibration
