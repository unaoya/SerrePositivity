module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportRestrictedPrismComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoCurryPointComparison

/-!
概要：元の全輸送比較の Hom 関手同型の成分を、元の実 prism の指定比較へ値まで戻す。
方針：元の endpointIso の curry の成分と同じ係数制限を使う。
規約：比較を選び直さない。使われ方：全第一辺の長辺比較の二成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} (p : E ⟶ B) [LeftFibration p] [Quasicategory L]
  {a b : B _⦋0⦌} (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T U : FiberTransportFamily (b := b) p f γ) (l : L _⦋0⦌)

/-- 元の全輸送の Hom 比較の同じ指定成分を、fiber の Kan 性から直接保持する。 -/
def fiberTransportFamilyMapIsoApp :
    VertexIso (T.map.app (Opposite.op ⦋0⦌) l) (U.map.app (Opposite.op ⦋0⦌) l) := by
  have := vertexFiber_kanComplex_of_leftFibration p b
  exact FunctorIso.app (FiberTransportFamily.mapIso p f γ h₁ T U) l

/-- 元の全輸送比較の同じ指定成分は、元の endpointIso の同じ係数制限。 -/
lemma fiberTransportFamilyMapIsoApp_heq_precomp :
    HEq (fiberTransportFamilyMapIsoApp p f γ h₁ T U l)
      ((FiberTransportFamily.endpointIso p f γ h₁ T U).precomp
        (lift (𝟙 K) (SSet.const l))) := by
  have := vertexFiber_kanComplex_of_leftFibration p b
  exact functorIso_curry_app_heq_precomp (FiberTransportFamily.endpointIso p f γ h₁ T U) l

/-- 元の全輸送比較の同じ指定成分は、元の二実 prism の同じ係数制限の指定比較。 -/
lemma fiberTransportFamilyMapIsoApp_heq_restricted :
    HEq (fiberTransportFamilyMapIsoApp p f γ h₁ T U l)
      (fiberTransportRestrictedPrismComparison p f γ h₁ T U (lift (𝟙 K) (SSet.const l))) :=
  (fiberTransportFamilyMapIsoApp_heq_precomp p f γ h₁ T U l).trans
    (heq_of_eq (fiberTransportRestrictedPrismComparison_eq_endpointIso p f γ h₁ T U
      (lift (𝟙 K) (SSet.const l)))).symm

end SerrePositivity.InfinityCategories.F2
