module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalBoundaryEquiv
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryKindExchange

/-!
模型。文献の定義との比較は後で
# 方向交換から得る垂直境界の同値

Berger–Fresse §2.2.7、M14 L09a。
既存のshuffleの方向交換で水平な三分岐を運び、入力面の全添字へまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C75：経路と指定頂点の両方を、同じ値を保って方向交換する。 -/
def markedCutExchangeEquiv (m q : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut m q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.MarkedCut q m :=
  Equiv.sigmaCongr (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleExchangeEquiv m q)
    (fun _ => finCongr (by omega : m + q + 1 = q + m + 1))

/-- C76：既存の種類の部分型を、交換した種類の部分型へ運ぶ。 -/
def boundaryKindExchangeEquiv (m q : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m q b ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind q m b.exchange :=
  Equiv.subtypeEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.markedCutExchangeEquiv m q) (fun t => by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1 t.2 = b ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind t.1.exchange
        (Fin.cast (by omega : m + q + 1 = q + m + 1) t.2) = b.exchange
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_exchange]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexKind.exchange_involutive.injective.eq_iff.symm)

/-- C77：入力の一面の添字は、全ての垂直な出力境界と同値。 -/
def verticalBoundaryFaceEquiv (m q : ℕ) :
    Fin (q + 2) × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryVertexOfKind m (q + 1) .vertical :=
  (Equiv.prodCongr (Equiv.refl _) (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleExchangeEquiv m q)).trans
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontalBoundaryFaceEquiv q m).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryKindExchangeEquiv (q + 1) m .horizontal))

/-- C78：垂直境界があれば、消す垂直次数が正である。 -/
lemma vertical_kind_pos {m q : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (k : Fin (m + q + 1))
    (hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s k = .vertical) : 0 < q := by
  have he : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s.exchange
      (Fin.cast (by omega : m + q + 1 = q + m + 1) k) = .horizontal := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_exchange, hk]
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.horizontal_kind_pos _ _ he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
