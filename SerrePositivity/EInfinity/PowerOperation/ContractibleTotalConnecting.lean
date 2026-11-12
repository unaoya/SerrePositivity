module

public import SerrePositivity.KST.Spectra.LoopZeroHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ContractibleTotalSequence

/-!
# 可縮な全空間の接続同値を全自然数次数で束ねる

DAG XIII §2.2 の Ω 比較で使う一般の補助。既存の接続写像そのものを用いる。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
open scoped Simplicial
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-- 零次数の fiber も含め、同じ接続写像が集合の同値を与える。 -/
def contractibleTotalConnectingEquiv {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) (hs : ∀ n, Subsingleton (KanHomotopy E n e))
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E)) (n : ℕ) :
    KanHomotopy B (n + 1) (p.app _ e) ≃
      KanHomotopy (KanFiber p (p.app _ e)) n (fiberPoint p e) :=
  Equiv.ofBijective (connecting p e n) (by
    cases n with
    | zero =>
      have := hs 0
      exact (SerrePositivity.KST.Spectra.connectingZeroEquiv p e hE).bijective
    | succ n =>
      have : Subsingleton (KanHomotopyGroup E n e) := hs (n + 1)
      have : Subsingleton (KanHomotopyGroup E (n + 1) e) := hs (n + 2)
      exact connectingHom_bijective_of_total_subsingleton p e n)

@[simp]
lemma contractibleTotalConnectingEquiv_apply {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) (hs : ∀ n, Subsingleton (KanHomotopy E n e))
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E))
    (n : ℕ) (a : KanHomotopy B (n + 1) (p.app _ e)) :
    contractibleTotalConnectingEquiv p e hs hE n a = connecting p e n a := rfl

end SerrePositivity.EInfinity.PowerOperation
