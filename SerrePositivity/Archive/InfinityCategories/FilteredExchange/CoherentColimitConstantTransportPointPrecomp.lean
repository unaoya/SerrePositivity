module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointPrism
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPrecompCompositionValue

/-!
概要：元の一点輸送比較の全初期値による前合成を、元の全輸送比較の実制限へ戻す。
方針：元の一点比較の指定値表示と、二段の前合成の合成則を使う。
規約：元の指定比較・実始域射・指定点を保持。使われ方：全三角形の長辺残余の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (b : SSet.Homotopy G J) {C : SSet.{u + 1}}
  (s : C ⟶ leftUnstraightening (coherentColimitRawConstantDiagram B G))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "w" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (Functor.obj SSet.uliftFunctor B) A)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s₀" => lift (𝟙 _) (SSet.const l)
local notation "e" => pointedIntervalTransportComparison P A w

/-- 元の一点比較を全初期値で前合成しても、元の全比較の同じ実係数制限になる。 -/
lemma coherentColimitConstantTransportPointIso_precomp_heq :
    HEq ((coherentColimitConstantTransportPointIso B b).precomp s)
      (FunctorIso.precomp e (lift s (SSet.const l))) := by
  rw [coherentColimitConstantTransportPointIso_eq_witness]
  have hp := functorIso_precomp_heq_of_heq (FunctorIso.precomp e s₀)
    (functorIsoOfEq (FunctorIso.precomp e s₀)
      (coherentColimitConstantTransport_endpoint_point B l) rfl)
    (coherentColimitConstantTransport_endpoint_point B l) rfl
    (functorIsoOfEq_heq _ _ _) s
  have hn : s ≫ s₀ = lift s (SSet.const l) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  exact hp.trans ((functorIso_precomp_precomp_heq e s₀ s).trans
    (functorIso_precomp_heq_of_map_eq e hn))

end SerrePositivity.InfinityCategories.F2
