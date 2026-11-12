module

public import SerrePositivity.EInfinity.PowerOperation.ContractibleTotalConnecting
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents

/-!
# 可縮な全空間を持つ正方形の固定 fiber の全基点比較

DAG XIII §2.2 の Ω 比較で使う一般の補助。底の指定基点での正次数だけを用い、
底の他の連結成分での同型は仮定しない。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

lemma contractibleFiberMap_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p] [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ q) (e : E _⦋0⦌)
    (hs : ∀ n, Subsingleton (KanHomotopy E n e))
    (hs' : ∀ n, Subsingleton (KanHomotopy E' n (f.app _ e)))
    (hr : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E))
    (hr' : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E')) (n : ℕ)
    (hg : Function.Bijective (KanHomotopyGroup.map (n := n) g
      (FibrationSquare.base_eq p q f g comm e))) :
    Function.Bijective (KanHomotopy.map n (FibrationSquare.fiberMap p q f g comm e)
      (FibrationSquare.fiberMap_point p q f g comm e)) := by
  let a := contractibleTotalConnectingEquiv p e hs hr n
  let b := contractibleTotalConnectingEquiv q (f.app _ e) hs' hr' n
  have hn : KanHomotopy.map n (FibrationSquare.fiberMap p q f g comm e)
      (FibrationSquare.fiberMap_point p q f g comm e) ∘ a =
      b ∘ KanHomotopyGroup.map g (FibrationSquare.base_eq p q f g comm e) := by
    funext x
    exact FibrationSquare.connecting_natural p q f g comm e n x
  apply (a.bijective_comp _).mp
  rw [hn]
  exact b.bijective.comp hg

lemma contractibleFiberMapOver_piIsomorphism {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (q : E' ⟶ B') [Fibration p] [Fibration q]
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ q)
    (hs : ∀ (e : E _⦋0⦌) n, Subsingleton (KanHomotopy E n e))
    (hs' : ∀ (e : E' _⦋0⦌) n, Subsingleton (KanHomotopy E' n e))
    (hr : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E))
    (hr' : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E'))
    (b : B _⦋0⦌) (b' : B' _⦋0⦌) (hbase : g.app _ b = b')
    (hg : ∀ n, Function.Bijective (KanHomotopyGroup.map (n := n) g hbase))
    (φ : KanFiber p b ⟶ KanFiber q b')
    (hφ : φ ≫ fiberι q b' = fiberι p b ≫ f) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism φ := by
  intro v n
  generalize he : (fiberι p b).app _ v = e
  have hb : p.app _ e = b := by
    rw [← he]
    exact fiber_vertex_base p b v
  have hb' : q.app _ (f.app _ e) = b' :=
    (FibrationSquare.base_eq p q f g comm e).symm.trans
      ((congrArg (g.app _) hb).trans hbase)
  subst b
  subst b'
  have heq : φ = FibrationSquare.fiberMap p q f g comm e := by
    apply fiber_hom_ext q (q.app _ (f.app _ e))
    exact hφ.trans (FibrationSquare.fiberMap_ι p q f g comm e).symm
  subst φ
  have hv : v = fiberPoint p e := by
    apply fiber_vertex_ext p (p.app _ e)
    exact he.trans (fiberι_point p e).symm
  subst v
  exact KanHomotopy.map_bijective_congr n (FibrationSquare.fiberMap p q f g comm e)
    rfl (FibrationSquare.fiberMap_point p q f g comm e).symm
    (FibrationSquare.fiberMap_point p q f g comm e) rfl
      (contractibleFiberMap_bijective p q f g comm e (hs e) (hs' _) hr hr' n (hg n))

end SerrePositivity.EInfinity.PowerOperation
