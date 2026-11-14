module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.MayPowerOperationZero
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroDiscrete
public import SerrePositivity.EInfinity.BarrattEccles.Theory

/-!
# 離散代数での May の P⁰ と Frobenius

May, Proposition 2.3(iii)・BS 著者版 Lemma 8.4 の補助。
零次の計算と、離散対象の零次以外のホモロジーの消滅で全整数次数を比較する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions (nerveVertex)
attribute [local instance] HasDerivedCategory.standard

abbrev mayDiscreteHoLoop (k : Type u) [CommRing k] (B : RingAlgebra k) (f : B ⟶ B) :=
  SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (discreteCAlgUnderEmbedding k))

lemma mayDiscretePiZero_frobenius (k : Type u) [CommRing k] (p : ℕ)
    (B : RingAlgebra k) (f : B ⟶ B) (hf : ∀ a : B.right, f.right.hom a = a ^ p)
    (a : ((barrattEcclesPi0 k).obj
      (SSet.HomotopyCategory.mk (atVertex (discreteCAlgUnderEmbedding k) (nerveVertex B)))).right) :
    ((barrattEcclesPi0 k).map (mayDiscreteHoLoop k B f)).right.hom a = a ^ p := by
  let d := barrattEcclesPi0_discrete k
  let t := ((Under.forget (CommRingCat.of k)).mapIso (d.app B)).commRingCatIsoToRingEquiv
  apply t.injective
  change (d.hom.app B).right.hom
    (((barrattEcclesPi0 k).map (mayDiscreteHoLoop k B f)).right.hom a) =
      (d.hom.app B).right.hom (a ^ p)
  have hh := congrArg (fun g => g.right.hom a) (d.hom.naturality f)
  change (d.hom.app B).right.hom
    (((barrattEcclesPi0 k).map (mayDiscreteHoLoop k B f)).right.hom a) =
      f.right.hom ((d.hom.app B).right.hom a) at hh
  exact hh.trans ((hf _).trans (map_pow (d.hom.app B).right.hom a p).symm)

/-- 離散入力では、全整数次数で指定 Frobenius の写像が同じ P⁰。 -/
lemma barrattEcclesPowerOp0_discrete (p : ℕ) [Fact p.Prime]
    (B : RingAlgebra (EInfinityPrimeField.{u} p)) (f : B ⟶ B)
    (hf : ∀ a : B.right, f.right.hom a = a ^ p) (n : ℤ) :
    let k := EInfinityPrimeField.{u} p
    let x := atVertex (discreteCAlgUnderEmbedding k) (nerveVertex B)
    (barrattEcclesPowerOp0 p n).app (SSet.HomotopyCategory.mk x) =
      (homotopyGroupsOnHo k (cAlgForgetDerived k) n).map (mayDiscreteHoLoop k B f) := by
  let k := EInfinityPrimeField.{u} p
  let x := atVertex (discreteCAlgUnderEmbedding k) (nerveVertex B)
  let z := SSet.HomotopyCategory.mk x
  by_cases hn : n = 0
  · subst n
    let e := (barrattEcclesPi0_forget k).app z
    ext b
    obtain ⟨a, rfl⟩ := e.toLinearEquiv.surjective b
    refine (barrattEcclesPowerOp0_zero p x a).trans ?_
    have hπ := mayDiscretePiZero_frobenius k p B f hf a
    have he := congrArg (fun g => g a)
      ((barrattEcclesPi0_forget k).hom.naturality (mayDiscreteHoLoop k B f))
    change e.hom (((barrattEcclesPi0 k).map (mayDiscreteHoLoop k B f)).right.hom a) = _ at he
    exact (congrArg e.hom hπ).symm.trans he
  · have hz := discreteCAlgUnderEmbedding_underlyingDisc k B (-n) (neg_ne_zero.mpr hn)
    let _ : Subsingleton ((homotopyGroupsOnHo k (cAlgForgetDerived k) n).obj z) :=
      ModuleCat.subsingleton_of_isZero hz
    ext a
    exact Subsingleton.elim _ _

end SerrePositivity.EInfinity.BarrattEccles
