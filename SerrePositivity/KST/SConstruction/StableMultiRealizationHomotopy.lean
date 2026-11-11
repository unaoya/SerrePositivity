module
public import SerrePositivity.KST.SConstruction.StableMultiRealizationEnrichedFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.ExactMapHomotopy

/-! # 全反復実現における関手同型の実ホモトピー
概要：完全関手の関手同型は、元の全有限反復 core S• 実現射の実ホモトピーになる。
方針：元の完全関手 core の辺を、同じ厳密豊穣実現関手の全 Hom 作用で写す。
規約：各行の局所化等号を対角に移す議論は使わない。使われ方：K-1/K-2 の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 元の全反復実現の Hom 作用は、通常射の元の関手頂点を回収する。 -/
lemma stableMultiRealizationEnrichedFunctor_vertex (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    ((stableMultiRealizationEnrichedFunctor r).map C D).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' C D F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((multiRealizationFunctor r).map (X := stableCategoryModel C)
        (Y := stableCategoryModel D)
        ⟨F.hom, @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩) := by
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌) PUnit.unit)
    (stableMultiRealizationEnrichedFunctor_hom r F)
  exact h

/-- 同じ完全関手の関手同型は、元の豊穣 Hom core の実際の辺を与える。 -/
lemma nonempty_stableExactFunctorIsoEdge {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    Nonempty (SSet.Edge (SimplicialCategory.homEquiv' C D F)
      (SimplicialCategory.homEquiv' C D G)) := by
  obtain ⟨a, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapCoreVertexIso e).hom
  exact ⟨SSet.Edge.ofTruncated a⟩

/-- 元の完全関手の関手同型から、同じ全反復実現射の実ホモトピーを構成する。 -/
def stableMultiRealizationHomotopyOfFunctorIso (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    SSet.Homotopy
      ((multiRealizationFunctor r).map (X := stableCategoryModel C)
        (Y := stableCategoryModel D)
        ⟨F.hom, @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩)
      ((multiRealizationFunctor r).map (X := stableCategoryModel C)
        (Y := stableCategoryModel D)
        ⟨G.hom, @preservesCofiberData_of_isExactFunctor _ _ G.hom G.isExact⟩) := by
  let a := Classical.choice (nonempty_stableExactFunctorIsoEdge e)
  let b := a.map ((stableMultiRealizationEnrichedFunctor r).map C D)
  have b' : SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((multiRealizationFunctor r).map (X := stableCategoryModel C)
        (Y := stableCategoryModel D)
        ⟨F.hom, @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((multiRealizationFunctor r).map (X := stableCategoryModel C)
        (Y := stableCategoryModel D)
        ⟨G.hom, @preservesCofiberData_of_isExactFunctor _ _ G.hom G.isExact⟩)) := {
    edge := b.edge
    src_eq := b.src_eq.trans (stableMultiRealizationEnrichedFunctor_vertex r F)
    tgt_eq := b.tgt_eq.trans (stableMultiRealizationEnrichedFunctor_vertex r G) }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge b'.toTruncated

end SerrePositivity.KST.SConstruction
