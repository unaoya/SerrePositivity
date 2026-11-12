module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakPointLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：元の弱い全 retract 図式を、分裂点を固定して cartesian fibration へ持ち上げる。
方針：射影辺の cartesian lift を選び、恒等長辺と最後の外側ホーンを充填する。
規約：元の二単体・潰した長辺・分裂点の全てを厳密に回収する。
使われ方：完備化の辺の関手圏における coherent retract の構成。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 指定した分裂点と元の全弱 retract 図式を cartesian fibration に持ち上げる。 -/
lemma cartesian_weakDiagram_lift_exists {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration p] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram Y) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (h : x ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakImagePoint ≫ d) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakRetractionDiagram X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakImagePoint ≫ e = x ∧ e ≫ p = d := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ d
  have hlong : stdSimplex.δ (1 : Fin 3) ≫ t = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫ x ≫ p := by
    dsimp only [t]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle_longEdge, Category.assoc, ← h]
  have hface : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) := by
    apply (SSet.yonedaEquiv (n := ⦋0⦌)).injective
    decide
  have hcollapse : stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse.{u} = 𝟙 Δ[0] := by
    apply SSet.yonedaEquiv.injective
    decide
  have hend : stdSimplex.δ (0 : Fin 2) ≫ (stdSimplex.δ (0 : Fin 3) ≫ t) = x ≫ p := by
    rw [← Category.assoc, hface, Category.assoc, hlong, ← Category.assoc,
      hcollapse, Category.id_comp]
  obtain ⟨f, hf, hfp, hfc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration.mem (p := p) |>.2
    (SSet.yonedaEquiv x) (stdSimplex.δ (0 : Fin 3) ≫ t) (by
      refine hend.trans ?_
      simpa only [Equiv.symm_apply_apply] using
        (SSet.yonedaEquiv_symm_comp (SSet.yonedaEquiv x) p))
  have hfx : stdSimplex.δ (0 : Fin 2) ≫ f = x := by
    simpa only [Equiv.symm_apply_apply] using hf
  let idEdge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫ x
  have hover : stdSimplex.δ (0 : Fin 2) ≫ idEdge = stdSimplex.δ (0 : Fin 2) ≫ f := by
    dsimp only [idEdge]
    rw [hfx, ← Category.assoc, hcollapse, Category.id_comp]
  let a := horn₂₂.isPushout.desc idEdge f hover
  have ha₁ : horn₂₂.ι₀₂ ≫ a = idEdge := horn₂₂.isPushout.inl_desc _ _ _
  have ha₀ : horn₂₂.ι₁₂ ≫ a = f := horn₂₂.isPushout.inr_desc _ _ _
  have hedge : SSet.yonedaEquiv horn₂₂.ι₁₂.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} 0 := by
    apply Subtype.ext
    decide
  have hfixed : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge 0) = SSet.yonedaEquiv f := by
    have hh := congrArg SSet.yonedaEquiv ha₀
    rwa [SSet.yonedaEquiv_comp, hedge] at hh
  have sq : CommSq a (horn 2 2).ι p t := by
    constructor
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, ha₁, ← Category.assoc, horn.ι_ι]
      exact hlong.symm
    · rw [← Category.assoc, ha₀, ← Category.assoc, horn.ι_ι]
      exact hfp
  have := hfc 0 a t hfixed sq
  have hl : stdSimplex.δ (1 : Fin 3) ≫ sq.lift = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse ≫ x := by
    rw [← horn.ι_ι_assoc (2 : Fin 3) 1 (by decide), sq.fac_left]
    exact ha₁
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc sq.lift x hl
  refine ⟨e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_imagePoint _ _ _, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDiagram_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_triangle, sq.fac_right]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakDesc_imagePoint]
    exact h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
