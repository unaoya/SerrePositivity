module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionEndpointWitness
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContractibleIsoComposition

/-!
概要：既存の相対延長の指定終点比較は、三つの元の延長に対して厳密に合成する。
方針：同じ可縮な選択空間で比較を合成し、中間の終点表示の移送を消去する。
規約：既存の witnessIso の値を保持。使われ方：単位三単体の共有面の比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A D C E F B : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {b : A ⟶ B}
  {i : D ⟶ A} {v : D ⟶ E} {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}

/-- 三つの元の全延長の既存の指定終点比較は、同じ直接比較へ厳密に合成する。 -/
lemma RelativeExtensionEndpointWitness.iso_trans
    (w₀ w₁ w₂ : RelativeExtensionEndpointWitness p b i v j q a)
    (hi : leftAnodyneExtensions i) (hv : v ≫ p = i ≫ b) (hj : j ≫ b = a ≫ q) :
    w₀.iso w₁ hi hv hj ≪≫ w₁.iso w₂ hi hv hj = w₀.iso w₂ hi hv hj := by
  let hK := relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv
  let Q := relativeFunctorExtensionEndpoint p b i v hv j q a hj
  let e (w : RelativeExtensionEndpointWitness p b i v j q a) :=
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (relativeFunctorExtensionEndpoint_vertex p b i v hv j q a hj
        w.extension w.over w.initial w.endpoint w.endpoint_over w.evaluate))
  let c₀₁ := VertexIso.map (hK.vertexIso (w₀.point hv) (w₁.point hv)) Q
  let c₁₂ := VertexIso.map (hK.vertexIso (w₁.point hv) (w₂.point hv)) Q
  let c₀₂ := VertexIso.map (hK.vertexIso (w₀.point hv) (w₂.point hv)) Q
  have hc : c₀₁ ≪≫ c₁₂ = c₀₂ :=
    contractibleVertexIso_map_trans hK (w₀.point hv) (w₁.point hv) (w₂.point hv) Q
  have ht := transportedVertexIso_trans (e w₀) (e w₁) (e w₂) c₀₁ c₁₂
  change ((e w₀).symm ≪≫ c₀₁ ≪≫ e w₁) ≪≫
      ((e w₁).symm ≪≫ c₁₂ ≪≫ e w₂) = (e w₀).symm ≪≫ c₀₂ ≪≫ e w₂
  exact ht.trans (congrArg (fun c => (e w₀).symm ≪≫ c ≪≫ e w₂) hc)

end SerrePositivity.InfinityCategories.F2
