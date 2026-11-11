module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuZeroArrowHomotopies

/-!
概要：元零角に隣接する二辺の端点成分固定ホモトピーを実関手同型にする。
方針：元恒等成分と同じ零角成分の可逆性を端点経路の上流判定へ渡す。
規約：元ホモトピーと指定端点の道を保持。使われ方：元上二胞体比較の二つの全辺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma zeroArrowIdentityInvertible (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 A)).toTruncated := by
  change IsIso (stableHoFunctor.map (𝟙 A))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "Z" => dgKInputStableValue R
  (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d))

/-- 概要：元実左辺の指定ホモトピーは関手全体の可逆な辺。
方針：元核の恒等と同じ toZeroCategory 成分の可逆性を使う。
規約：元二端点の道を保持。使われ方：元左辺の実関手同型。 -/
lemma dgOdotMilnorNuZeroLeftArrowHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuZeroLeftArrowHomotopy R d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths (dgOdotMilnorNuZeroLeftArrowHomotopy R d)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (K : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).toTruncated
    (zeroArrowIdentityInvertible (K)) (dgOdotMilnorNuZeroToZero_isInvertible R d)
    (dgOdotMilnorNuZeroLeftArrowHomotopy_paths R d).1
    (dgOdotMilnorNuZeroLeftArrowHomotopy_paths R d).2

/-- 概要：元実左辺と元標準零角への左辺の指定端点を保つ全関手同型。
方針：同じ実ホモトピーの可逆辺の類を同型として取る。
規約：元辺・元ホモトピーを保持。使われ方：元上比較 prism の左面。 -/
def dgOdotMilnorNuZeroLeftArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualLeft R d)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K))).edge) :=
  @asIso _ _ _ _ (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuZeroLeftArrowHomotopy R d)))
      (dgOdotMilnorNuZeroLeftArrowHomotopy_isInvertible R d)

/-- 概要：元実上辺の指定ホモトピーは関手全体の可逆な辺。
方針：同じ零角成分と元商の恒等成分の可逆性を使う。
規約：元二端点の道を保持。使われ方：元上辺の実関手同型。 -/
lemma dgOdotMilnorNuZeroTopArrowHomotopy_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgOdotMilnorNuZeroTopArrowHomotopy R d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths (dgOdotMilnorNuZeroTopArrowHomotopy R d)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z))).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (𝟙 (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}))).toTruncated
    (dgOdotMilnorNuZeroToZero_isInvertible R d) (zeroArrowIdentityInvertible (B))
    (dgOdotMilnorNuZeroTopArrowHomotopy_paths R d).1
    (dgOdotMilnorNuZeroTopArrowHomotopy_paths R d).2

/-- 概要：元実上辺と元標準零角からの上辺を指定成分で結ぶ全関手同型。
方針：同じ実ホモトピーの可逆辺から同型を取る。
規約：元辺・元端点の道を保持。使われ方：元上比較 prism の上面。 -/
def dgOdotMilnorNuZeroTopArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgOdotMilnorNuZeroActualTop R d)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (fromZeroCategory (B))).edge) :=
  @asIso _ _ _ _ (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (dgOdotMilnorNuZeroTopArrowHomotopy R d)))
      (dgOdotMilnorNuZeroTopArrowHomotopy_isInvertible R d)

/-- 概要：元実左辺の同じ全比較を元完備核・零角の Cat^perf の辺へ反映する。
方針：同じ完備包含の充満忠実性を使う。
規約：元二辺・元完備性を保持。使われ方：元全四角形比較の左境界。 -/
def dgOdotMilnorNuZeroPerfectLeftArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorNuZeroActualLeft R d)
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorFlatKernelInput R d))
      (dgKInputStableValue_isIdempotentComplete R
        (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)))).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (K))
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorFlatKernelInput R d))
      perfectZeroCategory_isIdempotentComplete).edge) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  rw [perfectStableArrow_inclusion, perfectStableArrow_inclusion]
  exact dgOdotMilnorNuZeroLeftArrowComparison R d

/-- 概要：元実上辺の同じ全比較を元完備零角・商の Cat^perf の辺へ反映する。
方針：同じ完備包含の充満忠実性を使う。
規約：元二辺・元完備性を保持。使われ方：元全四角形比較の上境界。 -/
def dgOdotMilnorNuZeroPerfectTopArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow (dgOdotMilnorNuZeroActualTop R d)
      (dgKInputStableValue_isIdempotentComplete R
        (dgFixedNullInput R (dgOdotMilnorFlatKernelInput R d)))
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (fromZeroCategory (B))
      perfectZeroCategory_isIdempotentComplete
      (dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d))).edge) := by
  apply perfectStableInfinityInclusion_isFullyFaithful.preimageFunctorIso
  rw [perfectStableArrow_inclusion, perfectStableArrow_inclusion]
  exact dgOdotMilnorNuZeroTopArrowComparison R d

end SerrePositivity.KST.SConstruction
