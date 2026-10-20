module

public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransport
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：同じ辺の族に対する対角輸送は、動く始点の関手同型を保つ。
方針：始点の単体的ホモトピーと同じ辺のパラメーターを普遍輸送の終点で同時に評価する。
規約：辺の族を固定したまま、パラメーターに依存する始点全体を比較する。
使われ方：pointed 四角形の中間点を、恒等射からの標準輸送へ一括で置き換える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 対角輸送は、動く始点の族の関手同型を全パラメーターで保つ。 -/
def diagonalFiberTransport_sourceIso {P E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g) (c : P ⟶ intervalMappingSpace a b) :
    FunctorIso (diagonalFiberTransport p f c) (diagonalFiberTransport p g c) := by
  have : KanComplex (vertexFiber p a) := vertexFiber_kanComplex_of_leftFibration p a
  have : KanComplex (vertexFiber p b) := vertexFiber_kanComplex_of_leftFibration p b
  let H := e.simplicialHomotopy
  let T := parametrizedFiberTransportFamily p a b
  let K : SSet.Homotopy (diagonalFiberTransport p f c) (diagonalFiberTransport p g c) :=
    { h := lift H.h (fst P (Δ[1] : SSet.{u}) ≫ c) ≫ T.endpoint
      h₀ := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg (fun z ↦ T.endpoint.app n (z, c.app n x))
          (congrArg (fun k ↦ k.app n x) H.h₀)
      h₁ := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg (fun z ↦ T.endpoint.app n (z, c.app n x))
          (congrArg (fun k ↦ k.app n x) H.h₁)
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  exact functorIsoOfSimplicialHomotopy K

end SerrePositivity.InfinityCategories
