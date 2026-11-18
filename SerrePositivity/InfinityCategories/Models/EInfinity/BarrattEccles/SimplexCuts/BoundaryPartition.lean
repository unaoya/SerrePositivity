module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryKinds

/-!
模型。文献の定義との比較は後で
# 指定頂点の境界種類による分割

Berger–Fresse §2.2.7、M14 L09a。
出力の頂点の有限型を、水平・垂直・混合・単独頂点へ分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

abbrev MarkedCut (m q : ℕ) := Σ _ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q, Fin (m + q + 1)

/-- 指定した種類の出力頂点。 -/
abbrev BoundaryVertexOfKind (m q : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind) :=
  {t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = b}

/-- C49：出力の指定頂点を四つの種類へ分ける全単射。 -/
def boundaryVertexPartitionEquiv (m q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q ≃
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .horizontal ⊕ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .vertical ⊕
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .mixed ⊕ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .isolated)) where
  toFun t :=
    if h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal then Sum.inl ⟨t, h⟩
    else if h' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .vertical then Sum.inr (Sum.inl ⟨t, h'⟩)
    else if h'' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .mixed then
      Sum.inr (Sum.inr (Sum.inl ⟨t, h''⟩))
    else Sum.inr (Sum.inr (Sum.inr ⟨t, by
      cases hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 <;> simp_all⟩))
  invFun := Sum.elim Subtype.val
    (Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val))
  left_inv t := by
    dsimp only
    split_ifs <;> rfl
  right_inv t := by
    rcases t with ⟨t, h⟩ | ⟨t, h⟩ | ⟨t, h⟩ | ⟨t, h⟩
    all_goals
      dsimp only
      simp [h]

/-- 語に依らない、出力面・係数面・入力面の全添字。 -/
abbrev UniversalBoundaryIndex (m q : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q ⊕ ((Fin (m + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m - 1) q) ⊕
    (Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q - 1)))

/-- C50：元のBFの全境界の添字を、語に依らない経路の添字へ移す。 -/
def boundaryBalanceIndexEquiv {r d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex u q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.UniversalBoundaryIndex (r + d) q :=
  Equiv.sumCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryPositionEquiv u q) (Equiv.refl _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
