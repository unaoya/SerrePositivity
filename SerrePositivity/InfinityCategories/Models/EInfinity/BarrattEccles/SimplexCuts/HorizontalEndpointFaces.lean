module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalSingletons
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalDeletion

/-!
模型。文献の定義との比較は後で
# 水平な始端・終端の境界の添字

Berger–Fresse §2.2.7、M14 L09a。
既存の水平辺挿入の同値に、出力の指定頂点と境界種類の条件を付ける。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C64：指定頂点を固定した経路の部分型を、指定頂点付き経路へ入れる同値。 -/
def fixedMarkedCutEquiv {m q : ℕ} (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind) (k : Fin (m + q + 1)) :
    {s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = b} ≃
      {t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = b ∧ t.2 = k} where
  toFun s := ⟨⟨s.val, k⟩, s.property, rfl⟩
  invFun t := ⟨t.val.1, by simpa only [t.property.2] using t.property.1⟩
  left_inv _ := rfl
  right_inv t := by
    rcases t with ⟨⟨s, k'⟩, h⟩
    apply Subtype.ext
    exact congrArg (fun j : Fin (m + q + 1) => (⟨s, j⟩ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q)) h.2.symm

/-- C65：水平な始端を持つ指定頂点は、最初の水平辺を挿入して得られる。 -/
def horizontalFirstFaceEquiv (m q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q ≃
    {t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut (m + 1) q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal ∧ t.2 = 0} :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q 0).trans
    ((Equiv.subtypeEquivRight fun s => by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_zero s (by omega)]
      by_cases h : (0 : Fin (m + 1 + q)) ∈ s.val <;> simp [h]).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fixedMarkedCutEquiv .horizontal 0))

/-- C66：水平な終端を持つ指定頂点は、最後の水平辺を挿入して得られる。 -/
def horizontalLastFaceEquiv (m q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q ≃
    {t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut (m + 1) q // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = .horizontal ∧
      t.2 = Fin.last (m + 1 + q)} := by
  let a : Fin (m + 1 + q) := ⟨m + q, by omega⟩
  refine (_root_.SerrePositivity.EInfinity.BarrattEccles.horizontalInsertionEquiv m q a).trans
    ((Equiv.subtypeEquivRight fun s => ?_).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.fixedMarkedCutEquiv .horizontal (Fin.last (m + 1 + q))))
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_last s (by omega)]
  have he : (⟨m + 1 + q - 1, by omega⟩ : Fin (m + 1 + q)) = a := by
    apply Fin.ext
    change m + 1 + q - 1 = m + q
    omega
  rw [he]
  by_cases h : a ∈ s.val <;> simp [h]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
