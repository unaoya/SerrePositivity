module

public import SerrePositivity.EInfinity.SimplexCuts.VerticalBoundaryEquiv
public import SerrePositivity.EInfinity.SimplexCuts.CornerFixedPoints

/-!
# 全境界の対合へ使う同値と角交換の法則

Berger–Fresse §2.2.7、M14 L09a。
正の次数の場合の挿入同値と、混合角の交換の既存の法則を同じ添字で用意する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C79：正の水平次数で、全ての係数添字を水平境界へ運ぶ。 -/
def horizontalBoundaryAllEquiv (m q : ℕ) (hm : 0 < m) :
    Fin (m + 1) × Cut (m - 1) q ≃ BoundaryVertexOfKind m q .horizontal := by
  cases m with
  | zero => omega
  | succ m => exact horizontalBoundaryFaceEquiv m q

/-- C80：正の垂直次数で、全ての入力面添字を垂直境界へ運ぶ。 -/
def verticalBoundaryAllEquiv (m q : ℕ) (hq : 0 < q) :
    Fin (q + 1) × Cut m (q - 1) ≃ BoundaryVertexOfKind m q .vertical := by
  cases q with
  | zero => omega
  | succ q => exact verticalBoundaryFaceEquiv m q

/-- C81：混合角の交換は境界種類を保つ。 -/
lemma mixed_kind_swapAtVertex {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .mixed) :
    boundaryVertexKind (swapAtVertex s k) k = .mixed :=
  (boundaryVertexKind_eq_mixed_iff _ _).mpr
    ((mixedVertex_swapAtVertex_iff s k).mpr ((boundaryVertexKind_eq_mixed_iff s k).mp hk))

/-- C82：指定頂点付き経路の角交換は、同じ型の上の対合。 -/
lemma vertexCornerPerm_involutive (m q : ℕ) : Function.Involutive (vertexCornerPerm m q) := by
  rintro ⟨s, k⟩
  change (⟨swapAtVertex (swapAtVertex s k) k, k⟩ : MarkedCut m q) = ⟨s, k⟩
  exact congrArg (fun t : Cut m q => (⟨t, k⟩ : MarkedCut m q))
    (swapAtVertex_involutive k s)

end SerrePositivity.EInfinity.SimplexCuts
