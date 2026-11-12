module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-! # 頂点条件の逆像への trivial Kan fibration の制限

元の射の頂点条件を反映する全部分圏へ制限しても、全単射に対する持ち上げを保つ。
元の射・任意の境界・全高次単体を保持する。相対 cofiber 補完の制限に用いる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 頂点条件を保つ射の全部分複体への制限。 -/
def fullPredicateMap {X Y : SSet.{u}} (p : X ⟶ Y)
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hp : ∀ x, P x → Q (p.app (Opposite.op ⦋0⦌) x)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift Q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ p)
    (fun x => hp x.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x))

/-- 制限射の包含後は元の射に一致する。 -/
lemma fullPredicateMap_ι {X Y : SSet.{u}} (p : X ⟶ Y)
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hp : ∀ x, P x → Q (p.app (Opposite.op ⦋0⦌) x)) :
    fullPredicateMap p P Q hp ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ p := rfl

/-- 頂点条件が正確な逆像なら、trivial Kan fibration の全境界持ち上げを制限できる。 -/
theorem fullPredicateMap_trivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hp : ∀ x, P x ↔ Q (p.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fullPredicateMap p P Q (fun x => (hp x).1)) where
  mem := by
    intro A B i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) i hi
    constructor
    intro a b sq
    let S : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) i p
        (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι) := ⟨by
      rw [Category.assoc, ← fullPredicateMap_ι p P Q (fun x => (hp x).1),
        ← Category.assoc, sq.w, Category.assoc]⟩
    have hv (v : B _⦋0⦌) : P (S.lift.app (Opposite.op ⦋0⦌) v) := by
      apply (hp _).2
      have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app S.fac_right (Opposite.op ⦋0⦌)) v
      change p.app _ (S.lift.app _ v) = (b.app _ v).val at he
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app _ v)
    refine CommSq.HasLift.mk' {
      l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P S.lift hv
      fac_left := ?_
      fac_right := ?_ }
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).1
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      exact S.fac_left
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι).1
      rw [Category.assoc, fullPredicateMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      exact S.fac_right

end SerrePositivity.KST.Fibration
