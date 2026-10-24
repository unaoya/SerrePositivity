module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.Functor
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianHomotopyEdges
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-!
概要：関手の同型による cocartesian 辺の保存条件の不変性。
方針：可逆な成分を持つホモトピーの正方形に合成と消去を適用する。
規約：始域の quasicategory 性や底上の同型という追加仮定を課さない。
使われ方：cocartesian 相対関手の全部分複体への制限同値の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 関手の同型は、各辺の像が cocartesian であるという条件を順方向へ移す。 -/
lemma isCocartesianEdge_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {f g : A ⟶ E} (h : FunctorIso f g) (e : A _⦋1⦌)
    (he : IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) e)) :
    IsCocartesianEdge p (g.app (Opposite.op ⦋1⦌) e) := by
  let H := h.simplicialHomotopy
  let K : (Δ[1] : SSet.{u}) ⊗ A ⟶ E := (β_ _ _).hom ≫ H.h
  have h₀ : prismEndpoint 0 A ≫ K = f := by
    dsimp only [K]
    rw [← Category.assoc, prismEndpoint_zero_braiding, H.h₀]
  have h₁ : prismEndpoint 1 A ≫ K = g := by
    dsimp only [K]
    rw [← Category.assoc, prismEndpoint_one_braiding, H.h₁]
  have hv (x : A _⦋0⦌) : IsCocartesianEdge p
      (K.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)) := by
    have hi := simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      h.edge h.edge_isInvertible x
    have hc := isCocartesianEdge_of_isInvertibleEdge p
      (simplicialHomotopyVertexEdge H x).toTruncated hi
    convert hc using 1
    change K.app _ (_, PinchedHom.constant x 1) =
      H.h.app _ ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
        homotopyIntervalEdge.edge)
    change H.h.app _ (PinchedHom.constant x 1, _) = _
    rw [pinchedConstant_one]
    congr 1
    apply Prod.ext
    · rfl
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hc := SerrePositivity.InfinityCategories.cocartesianHomotopy_targetEdge p K (SSet.yonedaEquiv.symm e)
    (by rw [h₀, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]; exact he) hv
  rwa [h₁, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hc

/-- 各辺の像の cocartesian 性は関手の同型で不変。 -/
lemma isCocartesianEdge_iff_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p]
    {f g : A ⟶ E} (h : FunctorIso f g) (e : A _⦋1⦌) :
    IsCocartesianEdge p (f.app (Opposite.op ⦋1⦌) e) ↔
      IsCocartesianEdge p (g.app (Opposite.op ⦋1⦌) e) :=
  ⟨isCocartesianEdge_of_functorIso p h e, isCocartesianEdge_of_functorIso p h.symm e⟩

/-- 全 cocartesian 辺の保存条件は関手の同型で不変。 -/
lemma preservesCocartesianEdges_iff_of_functorIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : A ⟶ B) (q : E ⟶ B) [InnerFibration q]
    {f g : A ⟶ E} (h : FunctorIso f g) :
    PreservesCocartesianEdges p q f ↔ PreservesCocartesianEdges p q g := by
  constructor <;> intro hf e he
  · exact (isCocartesianEdge_iff_of_functorIso q h e).mp (hf e he)
  · exact (isCocartesianEdge_iff_of_functorIso q h e).mpr (hf e he)

end SerrePositivity.InfinityCategories
