module

public import SerrePositivity.InfinityCategories.Core.ContractibleKan
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeSectionRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeHomLiftingFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightFibrationLocalFamily

/-!
概要：任意の coherent な局所辺の族について、元の相対 Hom の全境界充填性を証明する。
方針：元の比較射の可換性と Kan な写像空間の同値判定を使う。
規約：底と全パラメータは任意。使われ方：HTT 5.5.4.5(2) の局所辺の族の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 点ごとの辺の局所性は、同じ底の相対 Hom の各持ち上げ fiber の可縮性を与える。 -/
lemma localEdgeFamily_vertexFiber_isContractibleKan {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge ((functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)))) z)
    (sq : internalHom.PullbackObjObj (stdSimplex.δ (1 : Fin 2))
      (sliceOverProjection (SSet.yonedaEquiv.symm z)))
    (k : K _⦋0⦌) (b : sq.pt _⦋0⦌)
    (hb : sq.snd.app (Opposite.op ⦋0⦌) b = f.app (Opposite.op ⦋0⦌) k) :
    IsContractibleKan (vertexFiber sq.π b) := by
  let e := (functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)
  have he : functorVertex e = f.app (Opposite.op ⦋0⦌) k :=
    (functorVertexEquiv Δ[1] X).apply_symm_apply _
  have := (isLocalForHom_edge_iff_sectionRestriction_trivial e z).mp (h k)
  exact relativeHomFiber_isContractibleKan_of_restriction_trivial
    (stdSimplex.δ (1 : Fin 2)) (sliceOverProjection (SSet.yonedaEquiv.symm z))
      sq e b (hb.trans he.symm)

/-- 任意の coherent な局所辺の族に対し、元の相対 Hom の族は全境界を持ち上げる。 -/
lemma localEdgeFamily_relativeHom_trivial {K X : SSet.{u}} [Quasicategory X]
    (f : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (z : X _⦋0⦌)
    (h : ∀ k : K _⦋0⦌, IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge ((functorVertexEquiv Δ[1] X).symm (f.app (Opposite.op ⦋0⦌) k)))) z)
    (sq : internalHom.PullbackObjObj (stdSimplex.δ (1 : Fin 2))
      (sliceOverProjection (SSet.yonedaEquiv.symm z))) :
    TrivialKanFibration (relativeHomFamilyProjection (stdSimplex.δ (1 : Fin 2))
      (sliceOverProjection (SSet.yonedaEquiv.symm z)) sq f) :=
  relativeHomFamilyProjection_trivial _ _ _ _
    (localEdgeFamily_vertexFiber_isContractibleKan f z h sq)

end SerrePositivity.InfinityCategories.HomotopyLimits
