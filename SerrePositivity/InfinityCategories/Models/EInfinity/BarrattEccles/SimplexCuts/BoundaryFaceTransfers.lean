module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VerticalBoundaryEquiv
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CornerFixedPoints

/-!
模型。文献の定義との比較は後で
# 全境界の対合へ使う同値と角交換の法則

Berger–Fresse §2.2.7、M14 L09a。
正の次数の場合の挿入同値と、混合角の交換の既存の法則を同じ添字で用意する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C79：正の水平次数で、全ての係数添字を水平境界へ運ぶ。 -/
def horizontalBoundaryAllEquiv (m q : ℕ) (hm : 0 < m) :
    Fin (m + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m - 1) q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .horizontal := by
  cases m with
  | zero => omega
  | succ m => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv m q

/-- C80：正の垂直次数で、全ての入力面添字を垂直境界へ運ぶ。 -/
def verticalBoundaryAllEquiv (m q : ℕ) (hq : 0 < q) :
    Fin (q + 1) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m (q - 1) ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q .vertical := by
  cases q with
  | zero => omega
  | succ q => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticalBoundaryFaceEquiv m q

/-- C81：混合角の交換は境界種類を保つ。 -/
lemma mixed_kind_swapAtVertex {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .mixed) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex s k) k = .mixed :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_mixed_iff _ _).mpr
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.mixedVertex_swapAtVertex_iff s k).mpr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_mixed_iff s k).mp hk))

/-- C82：指定頂点付き経路の角交換は、同じ型の上の対合。 -/
lemma vertexCornerPerm_involutive (m q : ℕ) : Function.Involutive (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertexCornerPerm m q) := by
  rintro ⟨s, k⟩
  change (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex s k) k, k⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q) = ⟨s, k⟩
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q => (⟨t, k⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.swapAtVertex_involutive k s)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
