module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalInteriorFaces

/-!
# 同じ種類の境界の始点・内部・終点への分割

Berger–Fresse §2.2.7、M14 L09a。
既存の境界種類の部分型を、指定頂点の三つの位置へ分割する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 指定種類の始点の面。 -/
abbrev FirstBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = 0}

/-- 指定種類の内部の面。 -/
abbrev InteriorBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧
    0 < t.2.val ∧ t.2.val < m + q}

/-- 指定種類の終点の面。 -/
abbrev LastBoundaryFace (m q : ℕ) (b : BoundaryVertexKind) :=
  {t : MarkedCut m q // boundaryVertexKind t.1 t.2 = b ∧ t.2 = Fin.last (m + q)}

/-- C69：正の総次数では始点・内部・終点は互いに素で、全頂点を覆う。 -/
def boundaryEndpointPartitionEquiv (m q : ℕ) (b : BoundaryVertexKind) (hN : 0 < m + q) :
    BoundaryVertexOfKind m q b ≃ FirstBoundaryFace m q b ⊕
      (InteriorBoundaryFace m q b ⊕ LastBoundaryFace m q b) where
  toFun t :=
    if h0 : t.val.2 = 0 then Sum.inl ⟨t.val, t.property, h0⟩
    else if hl : t.val.2 = Fin.last (m + q) then Sum.inr (Sum.inr ⟨t.val, t.property, hl⟩)
    else Sum.inr (Sum.inl ⟨t.val, t.property, by
      have hk := t.val.2.isLt
      have h0' : t.val.2.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hl' : t.val.2.val ≠ m + q := fun h => hl (Fin.ext h)
      omega⟩)
  invFun := Sum.elim (fun t => ⟨t.val, t.property.1⟩)
    (Sum.elim (fun t => ⟨t.val, t.property.1⟩) (fun t => ⟨t.val, t.property.1⟩))
  left_inv t := by
    dsimp only
    split_ifs <;> rfl
  right_inv t := by
    rcases t with ⟨t, hb, h0⟩ | ⟨t, hb, hm⟩ | ⟨t, hb, hl⟩
    · dsimp only
      simp [h0]
    · have h0 : t.2 ≠ 0 := by
        intro h
        have he := congrArg Fin.val h
        change t.2.val = 0 at he
        omega
      have hl : t.2 ≠ Fin.last (m + q) := by
        intro h
        have he := congrArg Fin.val h
        change t.2.val = m + q at he
        omega
      dsimp only
      simp [h0, hl]
    · dsimp only
      simp [hl]
      omega

end SerrePositivity.EInfinity.SimplexCuts
