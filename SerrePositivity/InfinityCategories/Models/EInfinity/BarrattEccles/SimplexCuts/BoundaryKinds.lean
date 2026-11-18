module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerFixedPoints

/-!
模型。文献の定義との比較は後で
# 経路の指定頂点の境界の種類

Berger–Fresse §2.2.7、M14 L09a。
水平同方向・垂直同方向・混合角・零次の単独頂点を有限に分類する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

inductive BoundaryVertexKind
  | horizontal | vertical | mixed | isolated
  deriving DecidableEq

/-- C44：出力頂点を、係数面・入力面・混合角・単独頂点の四種類へ分ける。 -/
def boundaryVertexKind {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind :=
  if hN : 0 < m + q then
    if h0 : k.val = 0 then
      if (⟨0, hN⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
    else if hlast : k.val = m + q then
      if (⟨m + q - 1, by omega⟩ : Fin (m + q)) ∈ s.val then .horizontal else .vertical
    else
      let h : 0 < k.val ∧ k.val < m + q := ⟨by omega, by have hk := k.isLt; omega⟩
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerLeftEdge k h ∈ s.val then
        if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s.val then .horizontal else .mixed
      else if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cornerRightEdge k h ∈ s.val then .mixed else .vertical
  else .isolated

/-- C45：内部の種類の混合性は既存のMixedVertexと同じ条件。 -/
lemma boundaryVertexKind_eq_mixed_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .mixed ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex s k := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MixedVertex
  dsimp only
  split_ifs with hN h0 hh hlast hh hl hr hr
  all_goals
    first
    | simp only [false_iff]
      rintro ⟨h, hc⟩
      first | omega | tauto
    | constructor
      · intro _
        refine ⟨⟨by omega, by have hk := k.isLt; omega⟩, ?_⟩
        tauto
      · intro _
        rfl

/-- C46：単独頂点の種類は、水平次数も垂直次数も零のときだけ。 -/
lemma boundaryVertexKind_eq_isolated_iff {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (k : Fin (m + q + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .isolated ↔ m = 0 ∧ q = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind
  by_cases hN : 0 < m + q
  · rw [dite_eq_left hN]
    dsimp only
    split_ifs <;> simp_all <;> omega
  · rw [dite_eq_right hN]
    simp only [true_iff]
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
