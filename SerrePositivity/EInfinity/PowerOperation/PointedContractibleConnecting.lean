module

public import SerrePositivity.EInfinity.PowerOperation.ContractibleTotalConnecting
public import SerrePositivity.KST.Spectra.PointedZeroConnectingNaturality
public import SerrePositivity.KST.Spectra.PointedFibrationNaturality

/-!
# 指定基点での全次数の接続同値と自然性

DAG XIII §2.2 の Ω 比較で使う一般の補助。既存の零次数と正次数の接続写像を束ねる。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
  (pointedFiber pointedConnectingZero pointedConnectingHom pointedHomotopyMap
    pointedConnectingZero_natural pointedConnectingHom_natural)
open SerrePositivity.KST.Spectra.PointedFiberComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets

/-- 指定基点での接続写像。標的の零次数に群構造を要求しない。 -/
def pointedConnectingAll {E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B) [Fibration p.right]
    (n : ℕ) : KanHomotopy B.right (n + 1) B.basepoint →
      KanHomotopy (pointedFiber p).right n (pointedFiber p).basepoint :=
  match n with
  | 0 => pointedConnectingZero p
  | n + 1 => pointedConnectingHom p n

/-- 全空間が可縮なら、指定基点の同じ接続写像は同値になる。 -/
def pointedContractibleConnectingEquiv {E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B) [Fibration p.right]
    (hs : ∀ n, Subsingleton (KanHomotopy E.right n E.basepoint))
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E.right))
    (n : ℕ) : KanHomotopy B.right (n + 1) B.basepoint ≃
      KanHomotopy (pointedFiber p).right n (pointedFiber p).basepoint :=
  Equiv.ofBijective (pointedConnectingAll p n) (by
    cases n with
    | zero =>
      have := hs 0
      exact (((KanHomotopyGroup.equivOfIso 0 (Iso.refl B.right)
        (pointedMap_basepoint p)).symm.toEquiv.trans
          (SerrePositivity.KST.Spectra.connectingZeroEquiv p.right E.basepoint hE)).trans
            (SerrePositivity.KST.Spectra.pointedFiberZeroEquiv p).symm).bijective
    | succ n =>
      have : Subsingleton (KanHomotopyGroup E.right n E.basepoint) := hs (n + 1)
      have : Subsingleton (KanHomotopyGroup E.right (n + 1) E.basepoint) := hs (n + 2)
      exact (((KanHomotopyGroup.equivOfIso (n + 1) (Iso.refl B.right)
        (pointedMap_basepoint p)).symm.toEquiv.trans
          (connectingHomEquivOfTotalSubsingleton p.right E.basepoint n).toEquiv).trans
            (SerrePositivity.KST.Spectra.pointedFiberGroupEquiv p n).symm.toEquiv).bijective)

@[simp]
lemma pointedContractibleConnectingEquiv_apply {E B : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] (p : E ⟶ B) [Fibration p.right]
    (hs : ∀ n, Subsingleton (KanHomotopy E.right n E.basepoint))
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E.right))
    (n : ℕ) (a : KanHomotopy B.right (n + 1) B.basepoint) :
    pointedContractibleConnectingEquiv p hs hE n a = pointedConnectingAll p n a := rfl

/-- 全次数の接続写像は、指定された厳密な点付き正方形で自然。 -/
lemma pointedConnectingAll_natural {E B E' B' : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] [KanComplex E'.right] [KanComplex B'.right]
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p.right] [Fibration q.right]
    (f : E ⟶ E') (g : B ⟶ B') (h : p ≫ g = f ≫ q) (n : ℕ)
    (a : KanHomotopy B.right (n + 1) B.basepoint) :
    pointedHomotopyMap n (SerrePositivity.KST.Spectra.PointedFiberComparison.map p q f g h)
      (pointedConnectingAll p n a) =
      pointedConnectingAll q n (pointedHomotopyMap (n + 1) g a) := by
  cases n with
  | zero => exact pointedConnectingZero_natural p q f g h a
  | succ n => exact pointedConnectingHom_natural p q f g h n a

end SerrePositivity.EInfinity.PowerOperation
