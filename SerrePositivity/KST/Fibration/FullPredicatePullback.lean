module
public import SerrePositivity.KST.Fibration.FullPredicateRestriction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # 頂点条件を正確に反映する全部分図式の引き戻し

元の引き戻しの普遍性を、両射影の頂点条件の交わりで制限する。
quasicategory 性やモデル構造を仮定せず、全単体の射として証明する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の引き戻しの両射影の条件を反映する全部分複体も、同じ底上の引き戻し。 -/
lemma isPullback_fullPredicates {Z X Y T : SSet.{u}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {f : X ⟶ T} {g : Y ⟶ T} (h : IsPullback p q f g)
    (R : Z _⦋0⦌ → Prop) (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (hr : ∀ z, R z ↔ P (p.app (Opposite.op ⦋0⦌) z) ∧ Q (q.app (Opposite.op ⦋0⦌) z)) :
    IsPullback (fullPredicateMap p R P (fun z hz => ((hr z).1 hz).1))
      (fullPredicateMap q R Q (fun z hz => ((hr z).1 hz).2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ f) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι ≫ g) := by
  let a := fullPredicateMap p R P (fun z hz => ((hr z).1 hz).1)
  let b := fullPredicateMap q R Q (fun z hz => ((hr z).1 hz).2)
  let ιZ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Z R).ι
  let ιX := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι
  let ιY := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι
  have ha : a ≫ ιX = ιZ ≫ p := fullPredicateMap_ι _ _ _ _
  have hb : b ≫ ιY = ιZ ≫ q := fullPredicateMap_ι _ _ _ _
  have hw : a ≫ (ιX ≫ f) = b ≫ (ιY ≫ g) := by
    rw [← Category.assoc, ha, Category.assoc, h.w, ← Category.assoc, ← hb, Category.assoc]
  let raw (s : PullbackCone (ιX ≫ f) (ιY ≫ g)) : s.pt ⟶ Z :=
    h.lift (s.fst ≫ ιX) (s.snd ≫ ιY) (by simpa only [Category.assoc] using s.condition)
  have hraw₀ (s : PullbackCone (ιX ≫ f) (ιY ≫ g)) : raw s ≫ p = s.fst ≫ ιX :=
    h.lift_fst _ _ _
  have hraw₁ (s : PullbackCone (ιX ≫ f) (ιY ≫ g)) : raw s ≫ q = s.snd ≫ ιY :=
    h.lift_snd _ _ _
  let lift (s : PullbackCone (ιX ≫ f) (ιY ≫ g)) :
      s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Z R : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift R (raw s) (by
      intro v
      apply (hr _).2
      have he₀ := ConcreteCategory.congr_hom (NatTrans.congr_app (hraw₀ s) (Opposite.op ⦋0⦌)) v
      have he₁ := ConcreteCategory.congr_hom (NatTrans.congr_app (hraw₁ s) (Opposite.op ⦋0⦌)) v
      exact ⟨(congrArg P he₀).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (s.fst.app _ v)),
        (congrArg Q he₁).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (s.snd.app _ v))⟩)
  have hl (s : PullbackCone (ιX ≫ f) (ιY ≫ g)) : lift s ≫ ιZ = raw s :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_)
  · intro s
    apply (cancel_mono ιX).1
    rw [Category.assoc, ha, ← Category.assoc, hl, hraw₀]
  · intro s
    apply (cancel_mono ιY).1
    rw [Category.assoc, hb, ← Category.assoc, hl, hraw₁]
  · intro s m hm₀ hm₁
    apply (cancel_mono ιZ).1
    rw [hl]
    apply h.hom_ext
    · rw [hraw₀, Category.assoc, ← ha, ← Category.assoc, hm₀]
    · rw [hraw₁, Category.assoc, ← hb, ← Category.assoc, hm₁]

end SerrePositivity.KST.Fibration
