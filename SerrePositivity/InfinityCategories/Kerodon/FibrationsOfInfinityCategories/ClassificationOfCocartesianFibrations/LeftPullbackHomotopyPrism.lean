module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPath

/-!
概要：指定した底のホモトピーを、同じ始域上の二つの引き戻しの間のprismへ移す。
方針：既存の始点固定prismの持ち上げと、引き戻しの普遍性を適用する。
規約：HTT 2.1.1.6、Kerodon Tag 02RBのleft fibration版の既存持ち上げの計算法則。
  始域の射影と底の全ホモトピーを厳密に保持する。終点の射の同値性はここでは主張しない。
使われ方：R04の同じcoslice射影における、指定添字同型の代表ホモトピーの比較。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底の指定ホモトピーの持ち上げは、同じ始域上の引き戻し間の射と全prismを与える。 -/
@[cite HTT "2.1.1.6" (partial := special) "既存の始点固定prism持ち上げを引き戻しへ適用する法則。"]
lemma exists_leftPullbackHomotopyPrism {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {f g : K ⟶ B} (α : SSet.Homotopy f g) :
    ∃ (a : pullback p f ⟶ pullback p g)
      (H : SSet.Homotopy (pullback.fst p f) (a ≫ pullback.fst p g)),
      a ≫ pullback.snd p g = pullback.snd p f ∧
      H.h ≫ p = (pullback.snd p f ▷ (Δ[1] : SSet.{u})) ≫ α.h := by
  let A := pullback p f
  let π : A ⟶ K := pullback.snd p f
  let t := (β_ (Δ[1] : SSet.{u}) A).hom ≫ (π ▷ (Δ[1] : SSet.{u})) ≫ α.h
  have ht : pullback.fst p f ≫ p = prismEndpoint 0 A ≫ t := by
    have hi : prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫
        (π ▷ (Δ[1] : SSet.{u})) = π ≫ SSet.ι₀ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [show prismEndpoint 0 A ≫ t =
      (prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫
        (π ▷ (Δ[1] : SSet.{u}))) ≫ α.h by simp only [t, Category.assoc],
      hi, Category.assoc, α.h₀]
    exact pullback.condition
  obtain ⟨L, hL₀, hLp⟩ := leftFibration_lift_prism p (pullback.fst p f) t ht
  let R := (β_ A (Δ[1] : SSet.{u})).hom ≫ L
  have hR₀ : SSet.ι₀ ≫ R = pullback.fst p f := by
    exact hL₀
  have hRp : R ≫ p = (π ▷ (Δ[1] : SSet.{u})) ≫ α.h := by
    dsimp only [R, t] at *
    rw [Category.assoc, hLp, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hR₁ : (SSet.ι₁ ≫ R) ≫ p = π ≫ g := by
    rw [Category.assoc, hRp]
    have hi : SSet.ι₁ ≫ (π ▷ (Δ[1] : SSet.{u})) = π ≫ SSet.ι₁ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hi, Category.assoc, α.h₁]
  let a := pullback.lift (SSet.ι₁ ≫ R) π hR₁
  refine ⟨a, ⟨R, hR₀, ?_, ?_⟩, pullback.lift_snd _ _ _, hRp⟩
  · exact (pullback.lift_fst _ _ _).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
