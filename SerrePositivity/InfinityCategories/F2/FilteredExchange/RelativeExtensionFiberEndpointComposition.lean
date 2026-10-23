module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContractibleIsoComposition

/-!
概要：元の fiber 終点の三つの指定比較は、同じ直接比較へ厳密に合成する。
方針：可縮な全延長空間の比較へ値を戻し、同じ三終点の等式を保って合成する。
規約：比較を選び直さない。使われ方：元の下側輸送因子の中間選択の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三つの全延長と fiber 終点の指定比較は、元の直接比較へ厳密に合成する。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_trans {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W₀ W₁ W₂ : A ⟶ E) (h₀ : W₀ ≫ p = a) (h₁ : W₁ ≫ p = a) (h₂ : W₂ ≫ p = a)
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v) (hi₂ : i ≫ W₂ = v)
    (g₀ g₁ g₂ : C ⟶ vertexFiber p b)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p b)
    (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p b)
    (hj₂ : j ≫ W₂ = g₂ ≫ vertexFiberι p b) :
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
        W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁ ≪≫
      relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
        W₁ W₂ h₁ h₂ hi₁ hi₂ g₁ g₂ hj₁ hj₂ =
      relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
        W₀ W₂ h₀ h₂ hi₀ hi₂ g₀ g₂ hj₀ hj₂ := by
  let x₀ := relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W₀, h₀, hi₀⟩
  let x₁ := relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W₁, h₁, hi₁⟩
  let x₂ := relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W₂, h₂, hi₂⟩
  let Q := relativeExtensionFiberEndpoint p a i v hv j b hj
  let hK := relativeFunctorExtensionSpace_isContractibleKan p a i hi v hv
  have hc := contractibleVertexIso_map_trans hK x₀ x₁ x₂ Q
  have he₀ := (relativeExtensionFiberEndpoint_vertex p a i v hv j b hj
    W₀ h₀ hi₀ g₀ hj₀).symm
  have he₁ := (relativeExtensionFiberEndpoint_vertex p a i v hv j b hj
    W₁ h₁ hi₁ g₁ hj₁).symm
  have he₂ := (relativeExtensionFiberEndpoint_vertex p a i v hv j b hj
    W₂ h₂ hi₂ g₂ hj₂).symm
  have e₀₁ := relativeExtensionFiberEndpoint_witnessIso_heq_map p a i hi v hv j b hj
    W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁
  have e₁₂ := relativeExtensionFiberEndpoint_witnessIso_heq_map p a i hi v hv j b hj
    W₁ W₂ h₁ h₂ hi₁ hi₂ g₁ g₂ hj₁ hj₂
  have e₀₂ := relativeExtensionFiberEndpoint_witnessIso_heq_map p a i hi v hv j b hj
    W₀ W₂ h₀ h₂ hi₀ hi₂ g₀ g₂ hj₀ hj₂
  exact eq_of_heq ((vertexIso_trans_heq_of_heq _ _ _ _ he₀ he₁ he₂ e₀₁ e₁₂).trans
    ((heq_of_eq hc).trans e₀₂.symm))

end SerrePositivity.InfinityCategories.F2
