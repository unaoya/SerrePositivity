module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativeRestriction
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorRestrictionLifting
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverPrecomposition

/-!
概要：cocartesian 標的の相対関手空間の単射による制限は同値を右に持ち上げる。
方針：比較単射と試験同値の pushout-product を元の cocartesian fibration で持ち上げる。
規約：制限する単射自身の同値性は要求せず、元の底の quasicategory 性だけを用いる。
使われ方：区間 Hom 比較の境界固定の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- cocartesian 標的の相対内部 Hom の単射による制限は、単射な同値を持ち上げる。 -/
lemma kanEquivalenceLifting_relativeHom_of_cocartesian
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (i : D ⟶ A) [Mono i] (sq' : internalHom.PullbackObjObj i p) :
    F1B.KanEquivalenceLifting sq'.π := by
  intro K L j hj he
  have : Mono j := hj
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact cocartesianFibration_kanEquivalenceLifting p sq.ι
    (mono_pushoutObjObj_ι i j sq) (he.pushoutObjObj_right i sq)

/-- 底を固定した相対関手空間の任意の単射による制限も、単射な同値を持ち上げる。 -/
lemma kanEquivalenceLifting_relativeFunctorPre_of_cocartesian
    {A D E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    (a : A ⟶ B) (i : D ⟶ A) [Mono i] :
    F1B.KanEquivalenceLifting (relativeFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have h : F1B.KanEquivalenceLifting sq'.π :=
    kanEquivalenceLifting_relativeHom_of_cocartesian p i sq'
  intro K L j hj he
  have := h j hj he
  exact hasLiftingProperty_relativeFunctorPre p a i sq' j

/-- 元の底上の射による前合成の同じ制限は、単射な同値を持ち上げる。 -/
lemma kanEquivalenceLifting_relativeFunctorOverPre_of_cocartesian
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [CocartesianFibration p]
    {a b : Over B} (i : a ⟶ b) [Mono i.left] :
    F1B.KanEquivalenceLifting (relativeFunctorOverPre p i) := by
  have h (d : a.left ⟶ B) (hd : i.left ≫ b.hom = d) :
      F1B.KanEquivalenceLifting (relativeFunctorOverPre p
        (Over.homMk (U := Over.mk d) (V := b) i.left hd)) := by
    subst d
    exact kanEquivalenceLifting_relativeFunctorPre_of_cocartesian p b.hom i.left
  intro K L j hj he
  exact h a.hom i.w j hj he

end SerrePositivity.InfinityCategories
