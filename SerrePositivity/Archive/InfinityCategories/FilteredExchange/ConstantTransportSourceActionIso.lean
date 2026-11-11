module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantTransportUniversalSource
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalUniversalSourceAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapPostComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

/-!
概要：元の定値輸送比較を、全始点作用から恒等作用への一つの指定同型で保持する。
方針：普遍始点の定値比較の後合成作用を、元の一段作用へ戻す。
規約：元の定値比較の指定値を全成分で保持。使われ方：定値辺消去の始点自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a : B _⦋0⦌}
  (c : P ⟶ intervalMappingSpace a a) (hc : intervalMappingUncurry c = SSet.const a)
local notation "U" => diagonalFiberTransport_constantIso p (fst (vertexFiber p a) P)
  (snd (vertexFiber p a) P ≫ c)
  (intervalMappingUncurry_precomp_constant c hc (snd (vertexFiber p a) P))
local notation "β" => FunctorIso.precomp (FunctorIso.map_post U P) (functorPairRight (𝟙 P))

/-- 元の全定値輸送作用は、元の恒等作用への一つの指定関手同型を持つ。 -/
def diagonalConstantTransportSourceActionIso :
    FunctorIso (diagonalFiberSourceAction p c) (𝟙 ((ihom P).obj (vertexFiber p a))) :=
  functorIsoOfEq β (diagonalFiberSourceAction_universal p c) functorPairRight_id_fst

/-- 同じ全始点比較の各成分は、元の同じ始点族の指定定値輸送比較である。 -/
lemma diagonalConstantTransportSourceActionIso_app_heq (f : P ⟶ vertexFiber p a) :
    HEq ((diagonalConstantTransportSourceActionIso p c hc).app (functorVertex f))
      (diagonalFiberTransport_constantIso p f c hc) := by
  have hn := functorIso_app_heq_of_heq (diagonalConstantTransportSourceActionIso p c hc) β
    (diagonalFiberSourceAction_universal p c).symm functorPairRight_id_fst.symm
    (functorIsoOfEq_heq β (diagonalFiberSourceAction_universal p c) functorPairRight_id_fst)
    (functorVertex f)
  have hcomponent := functorIso_map_post_restricted_app_heq U (functorPairRight (𝟙 P))
    (functorVertex f) (lift f (𝟙 P)) (functorPairRight_vertex f (𝟙 P))
  exact hn.trans (hcomponent.trans (diagonalFiberTransport_constantIso_universal_precomp_heq p
    f c hc (intervalMappingUncurry_precomp_constant c hc (snd (vertexFiber p a) P))))

end SerrePositivity.InfinityCategories.F2
