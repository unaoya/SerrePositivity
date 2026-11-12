module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEndpointPrecomposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionNaturality

/-!
概要：同じ全相対延長の指定比較を実辺へ制限し、両端像を元の全評価へ戻す。
方針：全延長空間の指定同型を包含・前合成・端点評価の同じ合成へ写す。
規約：元の比較を保持。使われ方：同じ底辺を固定した全四角形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {D I E B A : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (β : D ⟶ B)
  (i : I ⟶ D) (hi : leftAnodyneExtensions i) (v : I ⟶ E) (hv : v ≫ p = i ≫ β)
  (W W' : D ⟶ E) (hW : W ≫ p = β) (hW' : W' ≫ p = β)
  (hWi : i ≫ W = v) (hWi' : i ≫ W' = v) (r : (Δ[1] : SSet.{u}) ⊗ A ⟶ D)
local notation "R" => relativeFunctorExtensionSpace p β i v hv
local notation "Eiso" => IsContractibleKan.vertexIso
  (relativeFunctorExtensionSpace_isContractibleKan p β i hi v hv)
  (relativeFunctorExtensionSpaceVertexEquiv p β i v hv (Subtype.mk W (And.intro hW hWi)))
  (relativeFunctorExtensionSpaceVertexEquiv p β i v hv (Subtype.mk W' (And.intro hW' hWi')))
local notation "ι" => relativeFunctorExtensionSpaceι p β i v hv

/-- 同じ全相対延長の元の指定比較を、同じ実辺へ制限した指定同型。 -/
def relativeExtensionPrismRestrictionIso :
    VertexIso (relativeFunctorVertex p (r ≫ β) (r ≫ W) (by rw [Category.assoc, hW]))
      (relativeFunctorVertex p (r ≫ β) (r ≫ W') (by rw [Category.assoc, hW'])) :=
  vertexIsoOfEq (VertexIso.map Eiso (ι ≫ relativeFunctorPre p β r))
    (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')

/-- 制限後の両端の指定像は、元の全延長空間での同じ端点評価の像。 -/
lemma relativeExtensionPrismRestriction_endpoint_heq (j : Fin 2) (z : B _⦋0⦌)
    (hz : (prismEndpoint j A ≫ r) ≫ β = SSet.const z) :
    HEq (VertexIso.map
      (relativeExtensionPrismRestrictionIso p β i hi v hv W W' hW hW' hWi hWi' r)
      (curry (relativePrismEvaluationEndpoint p (r ≫ β) j z
        ((Category.assoc (prismEndpoint j A) r β).symm.trans hz))))
      (VertexIso.map Eiso
        (relativeExtensionFiberEndpoint p β i v hv (prismEndpoint j A ≫ r) z hz)) := by
  have hs := vertexIsoOfEq_map_heq (VertexIso.map Eiso (ι ≫ relativeFunctorPre p β r))
    (relativeFunctorPre_vertex p β r W hW) (relativeFunctorPre_vertex p β r W' hW')
    (curry (relativePrismEvaluationEndpoint p (r ≫ β) j z
      ((Category.assoc (prismEndpoint j A) r β).symm.trans hz)))
  rw [vertexIso_map_comp] at hs
  refine hs.trans (vertexIso_map_heq Eiso ?_)
  unfold relativeExtensionFiberEndpoint
  rw [Category.assoc, relativePrismEvaluationEndpoint_restrict_eq_pre p β r j z hz]

/-- 制限後の端点像は、同じ元の二実延長の指定 fiber 終点比較に一致する。 -/
lemma relativeExtensionPrismRestriction_endpoint_heq_witness
    (j : Fin 2) (z : B _⦋0⦌)
    (hz : (prismEndpoint j A ≫ r) ≫ β = SSet.const z)
    (g g' : A ⟶ vertexFiber p z)
    (hg : (prismEndpoint j A ≫ r) ≫ W = g ≫ vertexFiberι p z)
    (hg' : (prismEndpoint j A ≫ r) ≫ W' = g' ≫ vertexFiberι p z) :
    HEq (VertexIso.map
      (relativeExtensionPrismRestrictionIso p β i hi v hv W W' hW hW' hWi hWi' r)
      (curry (relativePrismEvaluationEndpoint p (r ≫ β) j z
        ((Category.assoc (prismEndpoint j A) r β).symm.trans hz))))
      (relativeExtensionFiberEndpoint_witnessIso p β i hi v hv
        (prismEndpoint j A ≫ r) z hz W W' hW hW' hWi hWi' g g' hg hg') :=
  (relativeExtensionPrismRestriction_endpoint_heq p β i hi v hv
    W W' hW hW' hWi hWi' r j z hz).trans
      (relativeExtensionFiberEndpoint_witnessIso_heq_map p β i hi v hv
        (prismEndpoint j A ≫ r) z hz W W' hW hW' hWi hWi' g g' hg hg').symm

end SerrePositivity.InfinityCategories.F2
