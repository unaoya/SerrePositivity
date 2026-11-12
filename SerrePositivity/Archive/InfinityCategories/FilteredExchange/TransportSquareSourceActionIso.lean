module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareUniversalSource
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTwoStepUniversalAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapPostComponent
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

/-!
概要：元の全四角形比較を、始点の関手空間上の一つの指定同型として保持する。
方針：普遍始点の比較の後合成作用を取り、全二段作用へ端点だけを戻す。
規約：元の transportIso の指定値を全成分で保持。
使われ方：任意の係数上の始点同型への自然性。
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
variable {E B P : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
  (s : TransportIntervalSquare P a b c d)
local notation "R" => diagonalTwoStepSourceAction p
  (TransportIntervalSquare.bottom s) (TransportIntervalSquare.right s)
local notation "L" => diagonalTwoStepSourceAction p
  (TransportIntervalSquare.left s) (TransportIntervalSquare.top s)
local notation "U" => TransportIntervalSquare.transportIso p
  (TransportIntervalSquare.precomp s (snd (vertexFiber p a) P)) (fst (vertexFiber p a) P)
local notation "β" => FunctorIso.precomp (FunctorIso.map_post U P) (functorPairRight (𝟙 P))

/-- 元の四角形比較を、二つの元の全二段始点作用の間の同じ一つの同型で保持する。 -/
def transportIntervalSquareSourceActionIso : FunctorIso R L :=
  functorIsoOfEq β (diagonalTwoStepSourceAction_universal p s.bottom s.right)
    (diagonalTwoStepSourceAction_universal p s.left s.top)

/-- 同じ全始点作用の指定成分は、元の同じ始点族での transportIso と値まで一致する。 -/
lemma transportIntervalSquareSourceActionIso_app_heq (f : P ⟶ vertexFiber p a) :
    HEq ((transportIntervalSquareSourceActionIso p s).app (functorVertex f))
      (s.transportIso p f) := by
  have hnormalize := functorIso_app_heq_of_heq
    (transportIntervalSquareSourceActionIso p s) β
    (diagonalTwoStepSourceAction_universal p s.bottom s.right).symm
    (diagonalTwoStepSourceAction_universal p s.left s.top).symm
    (functorIsoOfEq_heq β (diagonalTwoStepSourceAction_universal p s.bottom s.right)
      (diagonalTwoStepSourceAction_universal p s.left s.top)) (functorVertex f)
  have hcomponent := functorIso_map_post_restricted_app_heq U (functorPairRight (𝟙 P))
    (functorVertex f) (lift f (𝟙 P)) (functorPairRight_vertex f (𝟙 P))
  exact hnormalize.trans (hcomponent.trans
    (transportIntervalSquare_transportIso_universal_precomp_heq p s f))

end SerrePositivity.InfinityCategories.F2
