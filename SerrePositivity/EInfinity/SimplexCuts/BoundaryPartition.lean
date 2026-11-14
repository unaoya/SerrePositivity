module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryKinds

/-!
# 指定頂点の境界種類による分割

Berger–Fresse §2.2.7、M14 L09a。
出力の頂点の有限型を、水平・垂直・混合・単独頂点へ分ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

abbrev MarkedCut (m q : ℕ) := Σ _ : Cut m q, Fin (m + q + 1)

/-- 指定した種類の出力頂点。 -/
abbrev BoundaryVertexOfKind (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b}

/-- C49：出力の指定頂点を四つの種類へ分ける全単射。 -/
def boundaryVertexPartitionEquiv (m q : ℕ) : MarkedCut m q ≃
    BoundaryVertexOfKind m q .horizontal ⊕ (BoundaryVertexOfKind m q .vertical ⊕
      (BoundaryVertexOfKind m q .mixed ⊕ BoundaryVertexOfKind m q .isolated)) where
  toFun t :=
    if h : boundaryVertexKind t.1 t.2 = .horizontal then Sum.inl ⟨t, h⟩
    else if h' : boundaryVertexKind t.1 t.2 = .vertical then Sum.inr (Sum.inl ⟨t, h'⟩)
    else if h'' : boundaryVertexKind t.1 t.2 = .mixed then
      Sum.inr (Sum.inr (Sum.inl ⟨t, h''⟩))
    else Sum.inr (Sum.inr (Sum.inr ⟨t, by
      cases hk : boundaryVertexKind t.1 t.2 <;> simp_all⟩))
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
  MarkedCut m q ⊕ ((Fin (m + 1) × Cut (m - 1) q) ⊕
    (Fin (q + 1) × Cut m (q - 1)))

/-- C50：元のBFの全境界の添字を、語に依らない経路の添字へ移す。 -/
def boundaryBalanceIndexEquiv {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    BoundaryBalanceIndex u q ≃ UniversalBoundaryIndex (r + d) q :=
  Equiv.sumCongr (outputBoundaryPositionEquiv u q) (Equiv.refl _)

end SerrePositivity.EInfinity.SimplexCuts
