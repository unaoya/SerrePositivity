module

public import SerrePositivity.InfinityCategories.F1B.KanFinalFiberRetraction
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianHomotopyEdges
public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian

/-!
概要：最終 fiber への cocartesian な輸送は cocartesian 辺を可逆辺へ送る。
方針：二つの三角形による消去で輸送後も cocartesian と示し、定値な底の上で可逆性を得る。
規約：最終 fiber への retraction は既存の実際の構成から取る。
使われ方：相対指数で cartesian になるべき終点指定の辺の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fiber への cocartesian なホモトピーの終端は cocartesian 辺を可逆辺へ送る。
方針：終端の辺の cocartesian 性を正方形から導き、定値な底の可逆性で検出する。
規約：射 p は quasicategory 間の inner fibration。
使われ方：最終 fiber の retraction の辺の判定。 -/
lemma kanCocartesianHomotopy_fiberTarget_invertible {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [InnerFibration p] (c : B _⦋0⦌)
    (R : E ⟶ vertexFiber p c) (H : (Δ[1] : SSet.{u}) ⊗ E ⟶ E)
    (h₀ : prismEndpoint 0 E ≫ H = 𝟙 E)
    (h₁ : prismEndpoint 1 E ≫ H = R ≫ vertexFiberι p c)
    (hv : ∀ x : E _⦋0⦌, IsCocartesianEdge p
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))
    (e : E _⦋1⦌) (he : IsCocartesianEdge p e) :
    IsInvertibleEdge (edgeOfSimplex (R.app (Opposite.op ⦋1⦌) e)) := by
  let f : (Δ[1] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm e
  have hf : IsCocartesianEdge p (SSet.yonedaEquiv (f ≫ prismEndpoint 0 E ≫ H)) := by
    rw [h₀, Category.comp_id]
    simpa only [f, Equiv.apply_symm_apply] using he
  have ht := kanCocartesianHomotopy_targetEdge p H f hf hv
  rw [h₁, SSet.yonedaEquiv_comp] at ht
  dsimp only [f] at ht
  rw [Equiv.apply_symm_apply] at ht
  change IsCocartesianEdge p ((R ≫ vertexFiberι p c).app (Opposite.op ⦋1⦌) e) at ht
  apply (isInvertibleEdge_vertexFiber_iff p c _).2
  apply isInvertibleEdge_of_isCocartesianEdge p _ ht
  have hb : p.app (Opposite.op ⦋1⦌)
      ((R ≫ vertexFiberι p c).app (Opposite.op ⦋1⦌) e) = PinchedHom.constant c 1 := by
    change (R ≫ vertexFiberι p c ≫ p).app (Opposite.op ⦋1⦌) e = _
    rw [vertexFiberι_comp, SSet.comp_const]
    rfl
  have hi := isEquivalencePathVertex_const c
  unfold IsEquivalencePathVertex at hi
  rw [intervalFunctorVertexEdge_functorVertex] at hi
  exact (isInvertibleEdge_congr hb).2 hi

/-- 概要：最終 fiber への厳密な retraction を cocartesian 辺を可逆にするように選べる。
方針：既存の cocartesian な輸送を選び、その終端の辺の判定を適用する。
規約：底は任意次元の標準単体。
使われ方：終点の図式から cartesian な相対指数の辺を作る入力。 -/
lemma exists_kanFinalFiberRetraction_inverting (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p] :
    ∃ R : E ⟶ vertexFiber p (stdSimplex.obj₀Equiv.symm (Fin.last n)),
      vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫ R = 𝟙 _ ∧
      ∀ e : E _⦋1⦌, IsCocartesianEdge p e →
        IsInvertibleEdge (edgeOfSimplex (R.app (Opposite.op ⦋1⦌) e)) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨R, H, hR, h₀, h₁, _, _, hv⟩ := exists_kanFinalFiberRetraction n p
  exact ⟨R, hR, fun e he ↦ kanCocartesianHomotopy_fiberTarget_invertible p _ R H h₀ h₁ hv e he⟩

/-- 概要：最終 fiber 上の図式は cocartesian 辺を可逆辺にする図式へ厳密に延長できる。
方針：cocartesian 辺を可逆にする retraction と図式を合成する。
規約：値域は quasicategory、最終 fiber での一致は厳密。
使われ方：Kerodon §5.3.6 の特殊な相対指数の辺の存在。 -/
lemma exists_kanFinalFiber_extension_inverting (n : ℕ) {E D : SSet.{u}} [Quasicategory D]
    (p : E ⟶ (Δ[n] : SSet.{u})) [CocartesianFibration p]
    (F : vertexFiber p (stdSimplex.obj₀Equiv.symm (Fin.last n)) ⟶ D) :
    ∃ G : E ⟶ D,
      vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫ G = F ∧
      ∀ e : E _⦋1⦌, IsCocartesianEdge p e →
        IsInvertibleEdge (edgeOfSimplex (G.app (Opposite.op ⦋1⦌) e)) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have := vertexFiber_quasicategory_of_innerFibration p
    (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨R, hR, he⟩ := exists_kanFinalFiberRetraction_inverting n p
  refine ⟨R ≫ F, ?_, ?_⟩
  · rw [← Category.assoc, hR, Category.id_comp]
  · intro e hc
    exact (isInvertibleEdge_congr (show
      ((edgeOfSimplex (R.app (Opposite.op ⦋1⦌) e)).map ((truncation 2).map F)).edge =
        (edgeOfSimplex ((R ≫ F).app (Opposite.op ⦋1⦌) e)).edge from rfl)).1 ((he e hc).map F)

end SerrePositivity.InfinityCategories
