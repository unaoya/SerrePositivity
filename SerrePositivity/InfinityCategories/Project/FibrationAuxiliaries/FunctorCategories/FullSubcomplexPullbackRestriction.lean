module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexInvertingRestriction
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：頂点条件の全部分複体への制限が pullback を保つ判定。
方針：元の pullback で単体を貼り合わせ、各頂点の二条件から所属条件を回収する。
規約：quasicategory 性は不要で、全次数の実際の pullback を証明する。
使われ方：指定辺を反転する関手の部分複体の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 頂点条件が両射影から回収できれば、全部分複体への制限も実際の pullback。 -/
lemma isPullback_fullSubcomplex_restriction {A B C D : SSet.{u}}
    {p : A ⟶ B} {q : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D}
    (h : IsPullback p q f g)
    (PA : A _⦋0⦌ → Prop) (PB : B _⦋0⦌ → Prop)
    (PC : C _⦋0⦌ → Prop) (PD : D _⦋0⦌ → Prop)
    (p' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB)
    (q' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC)
    (f' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD)
    (g' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD)
    (hp : p' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA).ι ≫ p)
    (hq : q' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA).ι ≫ q)
    (hf : f' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB).ι ≫ f)
    (hg : g' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC).ι ≫ g)
    (hP : ∀ a : A _⦋0⦌, PB (p.app _ a) → PC (q.app _ a) → PA a) :
    IsPullback p' q' f' g' := by
  have hw : p' ≫ f' = q' ≫ g' := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD).ι).mp
    calc
      (p' ≫ f') ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD).ι =
          (p' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB).ι) ≫ f := by
            rw [Category.assoc, hf, Category.assoc]
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA).ι ≫ (p ≫ f) := by rw [hp, Category.assoc]
      _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA).ι ≫ (q ≫ g) := by rw [h.w]
      _ = (q' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC).ι) ≫ g := by rw [hq, Category.assoc]
      _ = (q' ≫ g') ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices D PD).ι := by
        simp only [Category.assoc, hg]
  apply IsPullback.of_forall_isPullback_app
  intro d
  have hpv (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}).obj d) :
      (p'.app d a).val = p.app d a.val := by
    have he := congrArg
      (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}) ⟶ B ↦ k.app d a) hp
    exact he
  have hqv (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}).obj d) :
      (q'.app d a).val = q.app d a.val := by
    have he := congrArg
      (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA : SSet.{u}) ⟶ C ↦ k.app d a) hq
    exact he
  have hfv (b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB : SSet.{u}).obj d) :
      (f'.app d b).val = f.app d b.val := by
    have he := congrArg
      (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices B PB : SSet.{u}) ⟶ D ↦ k.app d b) hf
    exact he
  have hgv (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC : SSet.{u}).obj d) :
      (g'.app d c).val = g.app d c.val := by
    have he := congrArg
      (fun k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C PC : SSet.{u}) ⟶ D ↦ k.app d c) hg
    exact he
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app hw d, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply Types.ext_of_isPullback (h.app d)
    · exact (hpv a).symm.trans ((congrArg Subtype.val hab.1).trans (hpv b))
    · exact (hqv a).symm.trans ((congrArg Subtype.val hab.2).trans (hqv b))
  · intro b c hbc
    have he : f.app d b.val = g.app d c.val :=
      (hfv b).symm.trans ((congrArg Subtype.val hbc).trans (hgv c))
    obtain ⟨a, ha, hb⟩ := Types.exists_of_isPullback (h.app d) b.val c.val he
    have hmem : a ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A PA).obj d := by
      intro v
      apply hP
      · rw [p.naturality_apply v.op a, ha]
        exact b.property v
      · rw [q.naturality_apply v.op a, hb]
        exact c.property v
    exact ⟨⟨a, hmem⟩, Subtype.ext ((hpv _).trans ha), Subtype.ext ((hqv _).trans hb)⟩

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
