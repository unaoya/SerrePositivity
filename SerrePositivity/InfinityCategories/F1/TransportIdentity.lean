module

public import SerrePositivity.InfinityCategories.F1.EdgeTransport
public import SerrePositivity.InfinityCategories.F1.InvertibleCartesian

/-!
概要：恒等辺に沿う transport と恒等関手の比較。
方針：定値の prism の垂直辺が cocartesian であることを使う。
規約：底は quasicategory とし、全空間の quasicategory 性は inner fibration から得る。
使われ方：Kerodon Example 5.2.2.5、Construction 5.2.5.2 の単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：恒等関手は恒等辺に沿う cocartesian transport。
方針：第二射影からなる定値の prism を証人とする。
規約：恒等辺は二切断の恒等辺。
使われ方：Kerodon Example 5.2.2.5、transport の恒等との整合性。 -/
lemma isEdgeTransport_identity {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (b : B _⦋0⦌) :
    IsEdgeTransport p (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b)
      (𝟙 (vertexFiber p b)) := by
  have : Quasicategory X := quasicategory_of_innerFibration p
  let A := vertexFiber p b
  let H := snd (Δ[1] : SSet.{u}) A ≫ vertexFiberι p b
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · change (prismEndpoint 0 A ≫ snd (Δ[1] : SSet.{u}) A) ≫ vertexFiberι p b = _
    change (𝟙 A) ≫ vertexFiberι p b = _
    exact Category.id_comp _
  · change (prismEndpoint 1 A ≫ snd (Δ[1] : SSet.{u}) A) ≫ vertexFiberι p b = _
    rfl
  · have he : SSet.yonedaEquiv.symm
        (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b).edge =
        (SSet.const b : (Δ[1] : SSet.{u}) ⟶ B) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      change B.σ 0 b = PinchedHom.constant b 1
      exact (pinchedConstant_one b).symm
    change H ≫ p = _
    dsimp only [H]
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
    exact ((congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ B ↦ fst (Δ[1] : SSet.{u}) A ≫ f) he).trans
      (SSet.comp_const _ _)).symm
  · intro v
    change IsCocartesianEdge p ((vertexFiberι p b).app (Opposite.op ⦋1⦌)
      (PinchedHom.constant v 1))
    rw [pinchedConstant_map]
    exact isCocartesianEdge_constant p _

/-- 概要：選択した恒等辺の transport は恒等関手と同型。
方針：恒等関手の定値 prism と選択された transport の証人を比較する。
規約：同型は fiber 内の関手単体集合のホモトピー圏で得られる。
使われ方：Kerodon Construction 5.2.5.2、ホモトピー transport 表現の単位則。 -/
lemma edgeTransport_identity_iso {X B : SSet.{u}} [Quasicategory B] (p : X ⟶ B)
    [CocartesianFibration p] (b : B _⦋0⦌) :
    Nonempty (FunctorIso
      (edgeTransport p (SSet.Truncated.Edge.id (X := (truncation 2).obj B) b))
      (𝟙 (vertexFiber p b))) :=
  IsEdgeTransport.functorIso p _ (edgeTransport_isTransport p _) (isEdgeTransport_identity p b)

end SerrePositivity.InfinityCategories
