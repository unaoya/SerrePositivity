module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismFiber

/-!
概要：元の coherent 変換の全三角形を底の指定頂点で評価する。
方針：元の図式へ定値な底と一点パラメータを代入し、三辺の制限を保持する。
規約：充填や代表の選び直しなし。使われ方：各点の引き戻し錐と fiber 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：全単体の族へ元の底の一点を代入する。
方針：パラメータの一点と底を定値にする。
規約：元の全図式を制限。使われ方：指定二単体と三辺を同時に評価。 -/
def coherentTransformationPointDiagram {B : SSet.{u + 1}} {n : ℕ}
    (H : (Δ[n] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) : (Δ[n] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  lift (𝟙 Δ[n]) (SSet.const (b, stdSimplex.obj₀Equiv.symm 0)) ≫ H

/-- 概要：一点代入と全三角形の面への制限は厳密に可換。
方針：二成分を各次数で計算する。
規約：任意の面。使われ方：指定した三辺を保持する。 -/
lemma coherentTransformationPointDiagram_face {B : SSet.{u + 1}}
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (b : B _⦋0⦌) (i : Fin 3) :
    stdSimplex.δ i ≫ coherentTransformationPointDiagram H b =
      coherentTransformationPointDiagram
        ((stdSimplex.δ i ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H) b := by
  rfl

variable {B : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌}
  {y : (leftUnstraighteningTransformationSpace G J) _⦋0⦌}
  (T : CoherentTransformationVertexTriangle F G J x y) (b : B _⦋0⦌)

/-- 概要：元の三角形の第一辺の一点評価は元の第一変換の一点評価。
方針：元の第一面等式を制限。規約：射の等式。使われ方：各点の第一脚。 -/
lemma coherentTransformationPointDiagram_first :
    stdSimplex.δ 2 ≫ coherentTransformationPointDiagram T.diagram b =
      coherentTransformationPointDiagram
        (coherentTransformationFamilyDiagram (SSet.const x)) b := by
  rw [coherentTransformationPointDiagram_face, T.first]

/-- 概要：元の三角形の第二辺の一点評価は元の第二変換の一点評価。
方針：元の第二面等式を制限。規約：射の等式。使われ方：各点の第二脚。 -/
lemma coherentTransformationPointDiagram_second :
    stdSimplex.δ 0 ≫ coherentTransformationPointDiagram T.diagram b =
      coherentTransformationPointDiagram
        (coherentTransformationFamilyDiagram (SSet.const y)) b := by
  rw [coherentTransformationPointDiagram_face, T.second]

/-- 概要：元の三角形の長辺の一点評価は元の指定長変換の一点評価。
方針：元の長辺等式を制限。規約：射の等式。使われ方：二三角形の共通長辺を保持。 -/
lemma coherentTransformationPointDiagram_long :
    stdSimplex.δ 1 ≫ coherentTransformationPointDiagram T.diagram b =
      coherentTransformationPointDiagram
        (coherentTransformationFamilyDiagram (SSet.const T.diagonal)) b := by
  rw [coherentTransformationPointDiagram_face, T.long]

end SerrePositivity.InfinityCategories.F2
