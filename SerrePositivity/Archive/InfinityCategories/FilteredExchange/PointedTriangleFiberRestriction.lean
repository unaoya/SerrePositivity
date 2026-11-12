module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTransformationPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：元の全 pointed 三角形を始域 fiber へ制限し元の一点評価を底に保持する。
方針：fiber の包含と一点パラメータを代入し、元の射影式を制限する。
規約：全二単体・全単体パラメータを保持。使われ方：元の各点の錐と全空間作用の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の始域 fiber と一点パラメータの包含は底では指定点に定値。
方針：二射影と元の fiber 条件を計算する。
規約：全次数の射の等式。使われ方：全三角形の一点評価への制限。 -/
lemma vertexFiberParameterPoint_projection {E B : SSet.{u + 1}}
    (p : E ⟶ B) (b : B _⦋0⦌) :
    lift (vertexFiberι p b) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        (p ▷ (Δ[0] : SSet.{u + 1})) =
      SSet.const (b, stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, lift_fst, vertexFiberι_comp]
    rfl
  · rw [Category.assoc, whiskerRight_snd, lift_snd]
    rfl

/-- 概要：元の全三角形を始域 fiber に制限しても底は元の指定一点評価。
方針：元の射影等式と fiber の底固定式を全三角形で合成。
規約：二単体の全域での厳密な式。使われ方：元の指定二次整合を各点へ移す。 -/
lemma pointedTriangleFiberRestriction_projection {E B : SSet.{u + 1}}
    (p : E ⟶ B) (b : B _⦋0⦌)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (L : (Δ[2] : SSet.{u + 1}) ⊗ (E ⊗ (Δ[0] : SSet.{u + 1})) ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = (Δ[2] ◁ (p ▷ (Δ[0] : SSet.{u + 1}))) ≫ H) :
    (Δ[2] ◁ lift (vertexFiberι p b)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ L ≫ pointedSpaceProjection =
        fst (Δ[2] : SSet.{u + 1}) (vertexFiber p b) ≫ coherentTransformationPointDiagram H b := by
  rw [hL, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    vertexFiberParameterPoint_projection p b]
  rfl

end SerrePositivity.InfinityCategories.F2
