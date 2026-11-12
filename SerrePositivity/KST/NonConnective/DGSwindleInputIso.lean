module

public import SerrePositivity.KST.NonConnective.DGKappaSwindleInfinity
public import SerrePositivity.KST.SConstruction.DGFunctorClosedFamilyIso
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatFunctorCoreIso

/-!
概要：同じ厳密 dg swindle を、固定 K の元の入力 native Hom の実辺へ写す。
方針：全 Hom 自然な閉同型を dg 関手 Hom end の同型にし、同じ native core に含める。
規約：dg nerve 上の関手同型だけから、厳密 dg 入力の同型を結論しない。
使われ方：BGT Lem. 9.4 の固定連結 K への swindle の作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ dg cone 自体を、固定 K の厳密 dg 入力に束ねる。 -/
def dgKappaConeKInput : SConstruction.PerfDGInput R :=
  SConstruction.perfDGInputOf R (DGKappaCone R D I)

/-- 同じ実 swindle の両側逆を、元の dg 関手圏の全 Hom end に保持する。 -/
def dgKappaSwindleClosedFunctorIso :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaSwindleSource R D I) ≅
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaConeCountableSum R D I) :=
  SConstruction.dgFunctorClosedIsoFromFamily R (DGKappaCone R D I) (DGKappaCone R D I)
    (dgKappaSwindleSource R D I) (dgKappaConeCountableSum R D I)
    (dgKappaSwindleComponentIso R D I) (by
      intro X Y
      exact dgSwindleHom_enriched_naturality R D X.val Y.val)

/-- 同じ閉 dg 関手同型の native 辺は、元の dg 関手圏の nerve で可逆。 -/
lemma dgKappaSwindleFunctorEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I))
        (dgKappaSwindleClosedFunctorIso R D I).hom) := by
  let C := _root_.SerrePositivity.DifferentialGraded.DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C (dgKappaSwindleClosedFunctorIso R D I).hom
  have h : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R C).map (Truncated.HomotopyCategory₂.homMk e)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0_homMk, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed]
    infer_instance
  have : IsIso (Truncated.HomotopyCategory₂.homMk e) := isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R C)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso (Truncated.HomotopyCategory₂.homMk e)

/-- 固定 dg 入力の同じ native Kan Hom 内の、元の swindle 同型の実辺。 -/
def dgKappaSwindleNativeInputEdge :
    (SConstruction.dgFunctorNativeMappingSpace R (DGKappaCone R D I) (DGKappaCone R D I)).Edge
      (SConstruction.dgFunctorNativeMappingVertex R _ _ (dgKappaSwindleSource R D I))
      (SConstruction.dgFunctorNativeMappingVertex R _ _ (dgKappaConeCountableSum R D I)) where
  edge := ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ (dgKappaSwindleClosedFunctorIso R D I).hom).edge,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mpr
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).mp (dgKappaSwindleFunctorEdge_isInvertible R D I))⟩
  src_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ (dgKappaSwindleClosedFunctorIso R D I).hom).src_eq
  tgt_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R _ (dgKappaSwindleClosedFunctorIso R D I).hom).tgt_eq

end SerrePositivity.KST.NonConnective
