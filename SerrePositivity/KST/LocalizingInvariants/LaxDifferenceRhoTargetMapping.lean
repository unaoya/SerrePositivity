module

public import SerrePositivity.KST.LocalizingInvariants.ReflectiveTargetMapping
public import SerrePositivity.KST.LocalizingInvariants.TerminalTargetMapping
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceRho

/-!
概要：ρ(y) を終点とする元の lax pullback の写像空間正方形の C・D 二辺は同値。
方針：第一射影は選ばれた零対象、第二射影は v(y) なので終点・反射の比較を使う。
規約：元の p・q の pinchedHomMap を保持。使われ方：Tamme Prop. 11 の局所比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj)

lemma laxDifferenceRho_fst_vertex (y : E.obj _⦋0⦌) :
    (F2.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y) =
        (chosenZeroVertex C.obj).vertex :=
  LaxInclusion.fromD_fst_vertex p q (v.app (Opposite.op ⦋0⦌) y)

lemma laxDifferenceRho_snd_vertex (y : E.obj _⦋0⦌) :
    (F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y) = v.app (Opposite.op ⦋0⦌) y :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (laxDifferenceRho_snd p q v)
    (Opposite.op ⦋0⦌)) y

lemma laxDifferenceRho_fstMapping_equivalence (x : (laxCategory p q).obj _⦋0⦌)
    (y : E.obj _⦋0⦌) : IsSimplicialHomotopyEquivalence
    (pinchedHomMap p.hom ((F2.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌) x)
      ((F2.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌)
        ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y))) := by
  apply terminalTargetPinchedHomMap_equivalence
  · rw [laxDifferenceRho_fst_vertex]
    exact (chosenZeroVertex C.obj).isTerminal
  · rw [laxDifferenceRho_fst_vertex]
    exact (IsExactFunctor.preservesZero (F := p.hom) _ (chosenZeroVertex C.obj).isZero).2

lemma laxDifferenceRho_sndMapping_equivalence (a : QCatAdjunction q.hom v)
    (hv : IsFullyFaithful v) (x : (laxCategory p q).obj _⦋0⦌) (y : E.obj _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap q.hom ((F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌) x)
        ((F2.laxPullbackSnd p.hom q.hom).app (Opposite.op ⦋0⦌)
          ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y))) := by
  rw [laxDifferenceRho_snd_vertex]
  exact reflectiveTargetPinchedHomMap_equivalence a hv _ y

end SerrePositivity.KST.LocalizingInvariants
