module

public import SerrePositivity.InfinityCategories.F1.LeftPath

/-!
概要：left fibration の辺に沿う fiber 間の transport 関手の存在。
方針：始点 fiber の包含を底の辺の定値族に沿って持ち上げ、終点を取る。
規約：関手とは単体集合の射であり、単なる対象の写像ではない。
使われ方：Kerodon Proposition 5.2.2.8、Lemma 5.2.2.13 の left fibration の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の辺の定値族を prism の始点で制限すると辺の始点に定値。
方針：第一射影と端点の包含を計算し、Yoneda の評価を使う。
規約：パラメーターの単体集合 A は任意。
使われ方：Kerodon Lemma 5.2.2.13、transport の始点条件。 -/
lemma prismEdgeFamily_zero {A B : SSet.{u}} (e : B _⦋1⦌) :
    prismEndpoint 0 A ≫ (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e) =
      SSet.const (B.δ 1 e) := by
  rw [← Category.assoc]
  change SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
    SSet.yonedaEquiv.symm e = _
  rw [SSet.const_comp]
  congr 1
  rw [SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  rw [h]
  rfl

/-- 概要：底の辺の定値族を prism の終点で制限すると辺の終点に定値。
方針：第一射影と端点の包含を計算し、Yoneda の評価を使う。
規約：パラメーターの単体集合 A は任意。
使われ方：Kerodon Lemma 5.2.2.13、transport の標的 fiber の条件。 -/
lemma prismEdgeFamily_one {A B : SSet.{u}} (e : B _⦋1⦌) :
    prismEndpoint 1 A ≫ (fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e) =
      SSet.const (B.δ 0 e) := by
  rw [← Category.assoc]
  change SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
    SSet.yonedaEquiv.symm e = _
  rw [SSet.const_comp]
  congr 1
  rw [SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by decide
  rw [h]
  rfl

/-- 概要：left fibration の辺に沿う fiber 間の transport 関手は存在する。
方針：始点 fiber 全体をパラメーターとする prism を持ち上げ、その終点を fiber に入れる。
規約：底や全空間の quasicategory 性は不要で、全ての垂直辺は cocartesian。
使われ方：Kerodon Proposition 5.2.2.8 の left fibration の場合の存在。 -/
lemma leftFibration_exists_transport {X B : SSet.{u}} (p : X ⟶ B) [LeftFibration p]
    (e : B _⦋1⦌) :
    ∃ (F : vertexFiber p (B.δ 1 e) ⟶ vertexFiber p (B.δ 0 e))
      (H : (Δ[1] : SSet.{u}) ⊗ vertexFiber p (B.δ 1 e) ⟶ X),
      prismEndpoint 0 _ ≫ H = vertexFiberι p (B.δ 1 e) ∧
      prismEndpoint 1 _ ≫ H = F ≫ vertexFiberι p (B.δ 0 e) ∧
      H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e ∧
      ∀ x : (vertexFiber p (B.δ 1 e)) _⦋0⦌,
        IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)) := by
  let A := vertexFiber p (B.δ 1 e)
  let b := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e
  have hb : vertexFiberι p (B.δ 1 e) ≫ p = prismEndpoint 0 A ≫ b := by
    rw [vertexFiberι_comp, prismEdgeFamily_zero]
  obtain ⟨H, hH₀, hHp⟩ := leftFibration_lift_prism p (vertexFiberι p (B.δ 1 e)) b hb
  have ht : (prismEndpoint 1 A ≫ H) ≫ p = SSet.const (B.δ 0 e) := by
    rw [Category.assoc, hHp, prismEdgeFamily_one]
  let F := vertexFiberLift p (B.δ 0 e) (prismEndpoint 1 A ≫ H) ht
  exact ⟨F, H, hH₀, (vertexFiberLift_ι _ _ _ _).symm, hHp,
    fun _ ↦ isCocartesianEdge_of_leftFibration p _⟩

end SerrePositivity.InfinityCategories
