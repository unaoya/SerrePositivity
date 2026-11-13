module

public import SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundaryEquiv
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryKindExchange

/-!
# 方向交換から得る垂直境界の同値

Berger–Fresse §2.2.7、M14 L09a。
既存のshuffleの方向交換で水平な三分岐を運び、入力面の全添字へまとめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C75：経路と指定頂点の両方を、同じ値を保って方向交換する。 -/
def markedCutExchangeEquiv (m q : ℕ) : MarkedCut m q ≃ MarkedCut q m :=
  Equiv.sigmaCongr (BarrattEccles.shuffleExchangeEquiv m q)
    (fun _ => finCongr (by omega : m + q + 1 = q + m + 1))

/-- C76：既存の種類の部分型を、交換した種類の部分型へ運ぶ。 -/
def boundaryKindExchangeEquiv (m q : ℕ) (b : BoundaryVertexKind) :
    BoundaryVertexOfKind m q b ≃ BoundaryVertexOfKind q m b.exchange :=
  Equiv.subtypeEquiv (markedCutExchangeEquiv m q) (fun t => by
    change boundaryVertexKind t.1 t.2 = b ↔
      boundaryVertexKind t.1.exchange
        (Fin.cast (by omega : m + q + 1 = q + m + 1) t.2) = b.exchange
    rw [boundaryVertexKind_exchange]
    exact BoundaryVertexKind.exchange_involutive.injective.eq_iff.symm)

/-- C77：入力の一面の添字は、全ての垂直な出力境界と同値。 -/
def verticalBoundaryFaceEquiv (m q : ℕ) :
    Fin (q + 2) × Cut m q ≃ BoundaryVertexOfKind m (q + 1) .vertical :=
  (Equiv.prodCongr (Equiv.refl _) (BarrattEccles.shuffleExchangeEquiv m q)).trans
    ((horizontalBoundaryFaceEquiv q m).trans
      (boundaryKindExchangeEquiv (q + 1) m .horizontal))

/-- C78：垂直境界があれば、消す垂直次数が正である。 -/
lemma vertical_kind_pos {m q : ℕ} (s : Cut m q) (k : Fin (m + q + 1))
    (hk : boundaryVertexKind s k = .vertical) : 0 < q := by
  have he : boundaryVertexKind s.exchange
      (Fin.cast (by omega : m + q + 1 = q + m + 1) k) = .horizontal := by
    rw [boundaryVertexKind_exchange, hk]
    rfl
  exact horizontal_kind_pos _ _ he

end SerrePositivity.EInfinity.SimplexCuts
