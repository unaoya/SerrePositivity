module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CartesianEdgeTransport
public import SerrePositivity.InfinityCategories.Core.CocartesianHomotopyExtension

/-!
概要：終点と底を固定し、単射上で指定した Cartesian な輸送を全体へ延長する。
方針：反対圏の cocartesian な相対延長を使い、prism と全垂直辺を元へ戻す。
規約：元の指定輸送を厳密に保持する。使われ方：導来随伴の単位を表す比較正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- Cartesian な全垂直辺を持つ prism の反転は、全垂直辺が coCartesian。 -/
lemma reversePrism_vertical_isCocartesian {A E B : SSet.{u}} (p : E ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (hc : ∀ v : A _⦋0⦌, IsCartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)))
    (v : A.op _⦋0⦌) : IsCocartesianEdge (SSet.opFunctor.map p)
      ((reversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)) := by
  have h := (hc (SSet.opObjEquiv v)).op
  have he : SSet.opObjEquiv.symm (H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
        PinchedHom.constant (SSet.opObjEquiv v) 1)) =
    (reversePrism H).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1) := by
    change SSet.opObjEquiv.symm (H.app _ (_, _)) = SSet.opObjEquiv.symm (H.app _ (_, _))
    congr 2
    apply Prod.ext
    · apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    · rfl
  exact he ▸ h

/-- 単射上の指定輸送を、終点・底・全垂直辺の Cartesian 性を固定して延長する。 -/
lemma cartesianHomotopy_extend {A D E B : SSet.{u}} (p : E ⟶ B) [CartesianFibration p]
    (i : A ⟶ D) [Mono i] (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E) (f : D ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ D ⟶ B)
    (h₁ : prismEndpoint 1 A ≫ H = i ≫ f)
    (hf : f ≫ p = prismEndpoint 1 D ≫ β)
    (hHp : H ≫ p = (Δ[1] ◁ i) ≫ β)
    (hH : ∀ x : A _⦋0⦌, IsCartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ D ⟶ E,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 1 D ≫ F = f ∧ F ≫ p = β ∧
      ∀ x : D _⦋0⦌, IsCartesianEdge p
        (F.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)) := by
  have := SerrePositivity.InfinityCategories.F1B.cartesianFibration_op_toCocartesianHornFibration p
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have hm : Mono (SSet.opFunctor.map i) := inferInstance
  have h0 : prismEndpoint 0 A.op ≫ reversePrism H =
      SSet.opFunctor.map i ≫ SSet.opFunctor.map f := by
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 1 A ≫ H) = _
    rw [h₁, Functor.map_comp]
  have hfo : SSet.opFunctor.map f ≫ SSet.opFunctor.map p =
      prismEndpoint 0 D.op ≫ reversePrism β := by
    rw [reversePrism_endpoint]
    change _ = SSet.opFunctor.map (prismEndpoint 1 D ≫ β)
    rw [← Functor.map_comp, hf]
  have hpo : reversePrism H ≫ SSet.opFunctor.map p =
      (Δ[1] ◁ SSet.opFunctor.map i) ≫ reversePrism β := by
    rw [← reversePrism_postcomp, hHp, reversePrism_precomp]
  have hco : ∀ x : A.op _⦋0⦌, HasCocartesianHornLifting (SSet.opFunctor.map p)
      (edgeOfSimplex ((reversePrism H).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    exact (isCocartesianEdge_iff_hasCocartesianHornLifting _ _).1
      (reversePrism_vertical_isCocartesian p H hH x)
  obtain ⟨J, hJi, hJ0, hJp, hJc⟩ := cocartesianHomotopy_extend (SSet.opFunctor.map p)
    (SSet.opFunctor.map i) (reversePrism H) (SSet.opFunctor.map f) (reversePrism β)
    h0 hfo hpo hco
  refine ⟨unreversePrism (A := D) (Y := E) J, ?_, ?_, ?_, ?_⟩
  · rw [← unreversePrism_precomp, hJi, unreversePrism_reversePrism]
  · rw [unreversePrism_endpoint]
    change (SSet.opFunctorCompOpFunctorIso.app D).inv ≫
      SSet.opFunctor.map (prismEndpoint 0 D.op ≫ J) ≫ _ = _
    rw [hJ0]
    rfl
  · rw [← unreversePrism_postcomp, hJp, unreversePrism_reversePrism]
  · apply unreversePrism_vertical_isCartesian p J
    intro x
    exact (isCocartesianEdge_iff_hasCocartesianHornLifting _ _).2 (hJc x)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
