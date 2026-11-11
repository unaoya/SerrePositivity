module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.PrecompositionSimplexLocality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSourceIso
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：通常の圏の nerve 上の比較を有限鎖への引き戻しで判定する。
方針：各標準単体を有限鎖の nerve と同定し、nerve の充満性で底の射を関手として表示する。
規約：比較の始域と終域には充填性を要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、有限鎖上の scaffold 比較から一般の底への還元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：通常の圏の nerve 上の射は、全ての空でない有限鎖への引き戻しが前合成同値なら前合成同値。
方針：標準単体と有限鎖の nerve の同型を Over 圏へ持ち上げ、比較の自然性で同値性を移す。
規約：有限鎖は ULift (Fin (n+1)) とする。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、一般の通常の底の圏への拡張。 -/
lemma isPrecompositionEquivalence_of_pullback_finiteNerve
    {C : Type u} [Category.{u} C] {a b : Over (nerve C)} (f : a ⟶ b)
    (hfin : ∀ (n : ℕ) (H : ULift.{u} (Fin (n + 1)) ⥤ C),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap f (Over.mk (nerveMap H)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f.left := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_of_pullback_stdSimplex f
  intro n p
  let k : nerveFunctor.obj (Cat.of (ULift.{u} (Fin (n + 1)))) ⟶
      nerveFunctor.obj (Cat.of C) := (stdSimplex.isoNerve n).inv ≫ p
  let H := (nerveFunctor.preimage k).toFunctor
  have hH : nerveMap H = (stdSimplex.isoNerve n).inv ≫ p :=
    nerveFunctor.map_preimage _
  let e : Over.mk p ≅ Over.mk (nerveMap H) :=
    Over.isoMk (stdSimplex.isoNerve n) (by
      change (stdSimplex.isoNerve n).hom ≫ nerveMap H = p
      rw [hH, Iso.hom_inv_id_assoc])
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat f) e (hfin n H)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
