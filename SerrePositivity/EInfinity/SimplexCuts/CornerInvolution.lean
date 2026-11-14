module

public import SerrePositivity.EInfinity.SimplexCuts.CornerTraces
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryPositions

/-!
# 一頂点を指定した切断の角交換

Berger–Fresse §2.2.7、M14 L09a。
内部の指定頂点の前後の辺を交換する。端点は固定する。
これは出力項の混合角の部分に使う対合であり、全境界項の対合τではない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 内部頂点の直前の辺。 -/
def cornerLeftEdge {N : ℕ} (k : Fin (N + 1)) (h : 0 < k.val ∧ k.val < N) : Fin N :=
  ⟨k.val - 1, by omega⟩

/-- 内部頂点の直後の辺。 -/
def cornerRightEdge {N : ℕ} (k : Fin (N + 1)) (h : 0 < k.val ∧ k.val < N) : Fin N :=
  ⟨k.val, h.2⟩

/-- 指定頂点の角の交換。両端の頂点では恒等。 -/
def swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1)) : Cut m q :=
  if h : 0 < k.val ∧ k.val < m + q then
    s.swapSteps (cornerLeftEdge k h) (cornerRightEdge k h)
  else s

/-- C23：指定頂点の角の交換は対合。 -/
lemma swapAtVertex_involutive {m q : ℕ} (k : Fin (m + q + 1)) :
    Function.Involutive (fun s : Cut m q => swapAtVertex s k) := by
  intro s
  unfold swapAtVertex
  split_ifs <;> simp

/-- C24：切断とその指定頂点の角交換を有限型の置換にする。 -/
def vertexCornerPerm (m q : ℕ) : Equiv.Perm (Σ _ : Cut m q, Fin (m + q + 1)) :=
  Function.Involutive.toPerm (fun t => ⟨swapAtVertex t.1 t.2, t.2⟩) (by
    rintro ⟨s, k⟩
    exact congrArg (fun t : Cut m q => (⟨t, k⟩ : Σ _ : Cut m q, Fin (m + q + 1)))
      (swapAtVertex_involutive k s))

/-- C24の証明分割：頂点は動かさず、切断だけを交換する。 -/
lemma vertexCornerPerm_apply (m q : ℕ) (s : Cut m q) (k : Fin (m + q + 1)) :
    vertexCornerPerm m q ⟨s, k⟩ = ⟨swapAtVertex s k, k⟩ := rfl

/-- C25：出力の色と面番号へ戻した角交換の置換。 -/
def outputCornerPerm {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    Equiv.Perm (OutputBoundaryIndex u q) :=
  (outputBoundaryPositionEquiv u q).trans
    ((vertexCornerPerm (r + d) q).trans (outputBoundaryPositionEquiv u q).symm)

/-- C25の証明分割：出力の添字へ運んだ後も対合。 -/
lemma outputCornerPerm_involutive {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :
    Function.Involutive (outputCornerPerm u q) := by
  intro t
  apply (outputBoundaryPositionEquiv u q).injective
  simp only [outputCornerPerm, Equiv.trans_apply, Equiv.apply_symm_apply]
  rcases (outputBoundaryPositionEquiv u q) t with ⟨s, k⟩
  simp only [vertexCornerPerm_apply, swapAtVertex_involutive k s]

end SerrePositivity.EInfinity.SimplexCuts
