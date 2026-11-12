module

public import SerrePositivity.EInfinity.PowerOperation.PointedContractibleConnecting

/-!
# 可縮な全空間を持つ正方形での次数移動の検出

DAG XIII §2.2 の Ω 比較に使う一般の補助。接続写像の自然性と全単射性だけを使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra (pointedHomotopyMap)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

lemma pointedConnecting_bijective_iff {E B E' B' : PointedSimplicialSet.{u}}
    [KanComplex E.right] [KanComplex B.right] [KanComplex E'.right] [KanComplex B'.right]
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p.right] [Fibration q.right]
    (f : E ⟶ E') (g : B ⟶ B') (h : p ≫ g = f ≫ q)
    (hE : ∀ n, Subsingleton (KanHomotopy E.right n E.basepoint))
    (hE' : ∀ n, Subsingleton (KanHomotopy E'.right n E'.basepoint))
    (hr : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E.right))
    (hr' : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E'.right)) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n
      (KST.Spectra.PointedFiberComparison.map p q f g h)) ↔
      Function.Bijective (pointedHomotopyMap (n + 1) g) := by
  let e := pointedContractibleConnectingEquiv p hE hr n
  let e' := pointedContractibleConnectingEquiv q hE' hr' n
  let φ := KST.Spectra.PointedFiberComparison.map p q f g h
  have hn : pointedHomotopyMap n φ ∘ e = e' ∘ pointedHomotopyMap (n + 1) g := by
    funext a
    exact pointedConnectingAll_natural p q f g h n a
  exact (e.bijective_comp _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective hn)).trans (e'.comp_bijective _))

end SerrePositivity.EInfinity.PowerOperation
