module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber

/-!
概要：指定区間に沿う余錐を端点に制限し、元の二単体からホモトピー圏の合成を読む。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

namespace SerrePositivity.InfinityCategories.Sheaves

private def intervalEdge :
    (Δ[1] : SSet.{u}).Edge (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))) where
  edge := SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))
  src_eq := by
    change (Δ[1] : SSet.{u}).δ 1 (SSet.yonedaEquiv (𝟙 _)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]
  tgt_eq := by
    change (Δ[1] : SSet.{u}).δ 0 (SSet.yonedaEquiv (𝟙 _)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, Category.comp_id]

open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

def normalizedCosliceFiberEdge {X : SSet.{u}} (a v : X _⦋0⦌)
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm a)) v) _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj X) a v where
  edge := (cosliceFiberEdge _ _ s).edge
  src_eq := (cosliceFiberEdge _ _ s).src_eq.trans (SSet.yonedaEquiv.apply_symm_apply a)
  tgt_eq := (cosliceFiberEdge _ _ s).tgt_eq

/-- 指定区間に沿う余錐を端点に制限し、元の二単体からホモトピー圏の合成を読む。
Kerodon §4.6 の slice と join。HTT 4.1.3.1 に使う区間上の照合。 -/
lemma cosliceIntervalNormalized_homMk
    {X : SSet.{u}} {a b : X _⦋0⦌} (e : X.Edge a b)
    (c : JoinCocone (SSet.yonedaEquiv.symm e.edge)) :
    let η := SSet.yonedaEquiv.symm e.edge
    let v := c.vertex
    let he₀ := e.δ_one_yonedaEquiv_symm
    let he₁ := e.δ_zero_yonedaEquiv_symm
    let r₀ := sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder he₀)
    let r₁ := sliceUnderRestrict η (stdSimplex.δ (0 : Fin 2)) ≫
      eqToHom (congrArg sliceUnder he₁)
    ∀ (s₀ : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm a)) v) _⦋0⦌)
      (s₁ : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm b)) v) _⦋0⦌),
    s₀.val = r₀.app (Opposite.op ⦋0⦌) c →
    s₁.val = r₁.app (Opposite.op ⦋0⦌) c →
    Truncated.HomotopyCategory.homMk e.toTruncated ≫
      Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge b v s₁) =
        Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge a v s₀) := by
  intro η v he₀ he₁ r₀ r₁ s₀ s₁ h₀ h₁
  let e₀ : (Δ[1] : SSet.{u}).Edge (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))) := intervalEdge
  let T := coconeVertexLegCompStruct c e₀
  have he : (e₀.map η).edge = e.edge := by
    change η.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 Δ[1])) = e.edge
    rw [← SSet.yonedaEquiv_comp, Category.id_comp]
    exact SSet.yonedaEquiv.apply_symm_apply e.edge
  have hf₀ : (coconeVertexLeg c (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))).edge =
      (normalizedCosliceFiberEdge a v s₀).edge := by
    change _ = SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s₀.val.val)
    rw [h₀]
    change _ = SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (((eqToHom (congrArg sliceUnder he₀)).app (Opposite.op ⦋0⦌))
        ((sliceUnderRestrict η (stdSimplex.δ (1 : Fin 2))).app _ c)).val)
    rw [sliceUnder_eqToHom_app_val he₀]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))) (𝟙 Δ[0]) ≫ c.val) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hf₁ : (coconeVertexLeg c (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)))).edge =
      (normalizedCosliceFiberEdge b v s₁).edge := by
    change _ = SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s₁.val.val)
    rw [h₁]
    change _ = SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (((eqToHom (congrArg sliceUnder he₁)).app (Opposite.op ⦋0⦌))
        ((sliceUnderRestrict η (stdSimplex.δ (0 : Fin 2))).app _ c)).val)
    rw [sliceUnder_eqToHom_app_val he₁]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ joinMap
      (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)))) (𝟙 Δ[0]) ≫ c.val) = _
    rw [Equiv.symm_apply_apply]
    rfl
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    ⟨T.simplex, T.d₂.trans he, T.d₀.trans hf₁, T.d₁.trans hf₀⟩

end SerrePositivity.InfinityCategories.Sheaves
