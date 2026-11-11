module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges

/-! # 実 dg 関手 Hom end の閉同型を同じ native core の辺にする
概要：全次数自然変換 end の元の閉同型から、同じ native 写像空間の実辺を得る。
方針：元の閉順射の H⁰ 類の可逆性を反映し、同じ dg nerve の core へ含める。
規約：対象別の同型だけを入力にしない。使われ方：固定 S における二つの厳密入力射の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories SSet
variable (R : Type u) [CommRing R] (D E : Type v) [DGCategory R D] [DGCategory R E]
  [Small.{u} D] (F G : DGFunctor R D E)
  (e : ForgetEnrichment.of (Complex R) F ≅ ForgetEnrichment.of (Complex R) G)

/-- 元の Hom end 内の閉同型の順射は、同じ dg 関手圏の nerve の可逆辺。 -/
lemma dgFunctorClosedIsoEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (DGFunctor R D E) e.hom) := by
  have h : IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (DGFunctor R D E)).functor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (DGFunctor R D E) e.hom))) := by
    erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_map_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
    exact ((toHomotopy R (DGFunctor R D E)).mapIso e).isIso_hom
  exact isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (DGFunctor R D E)).functor

/-- 同じ閉同型の元の順射を、そのまま同じ native core 内の実辺として保持する。 -/
def dgFunctorClosedIsoNativeEdge :
    (dgFunctorNativeMappingSpace R D E).Edge
      (dgFunctorNativeMappingVertex R D E F) (dgFunctorNativeMappingVertex R D E G) where
  edge := ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ e.hom).edge,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mp
        (dgFunctorClosedIsoEdge_isInvertible R D E F G e))⟩
  src_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ e.hom).src_eq
  tgt_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ e.hom).tgt_eq

/-- 同じ native core の辺を含めると、元の Hom end の指定閉順射の辺を回収する。 -/
lemma dgFunctorClosedIsoNativeEdge_inclusion :
    (dgFunctorClosedIsoNativeEdge R D E F G e).edge.val =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (DGFunctor R D E) e.hom).edge := rfl

end SerrePositivity.KST.SConstruction
