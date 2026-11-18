module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightShiftPrism

/-!
概要：同じcoslice内の指定ホモトピーを、頂点固定の全錐prismへ戻す。
方針：右直積とjoinの既存の比較をcosliceのuncurryで後合成する。
規約：HTT 5.1.5.6、Kerodon Tag 02Y9の局所錐比較で使う既存構成の境界の法則。
使われ方：R04で添字の指定ホモトピーを元の標準錐の族に移し、余単位との合成を照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

private lemma joinTensorRight_zero (A B : SSet.{u}) :
    (SSet.ι₀ : join A B ⟶ join A B ⊗ Δ[1]) ≫ joinTensorRight A B Δ[1] =
      joinMap (𝟙 A) (SSet.ι₀ : B ⟶ B ⊗ Δ[1]) := by
  have he (X : SSet.{u}) :
      fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₀ = X ◁ (stdSimplex.δ (1 : Fin 2)) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    apply Prod.ext
    · rfl
    · apply stdSimplex.ext
      intro i
      apply Fin.ext
      change (0 : ℕ) = ((SimplexCategory.δ (1 : Fin 2)).toOrderHom (t i)).val
      rw [Fin.eq_zero (t i)]
      rfl
  apply (cancel_epi (fst (join A B) (Δ[0] : SSet.{u}))).mp
  rw [← Category.assoc, he, joinTensorRight_parameter, ← he B]
  have hc : joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u}) ≫ SSet.ι₀) =
      joinMap (𝟙 A) (fst B (Δ[0] : SSet.{u})) ≫ joinMap (𝟙 A) SSet.ι₀ := by
    simpa only [Category.id_comp] using
      joinMap_comp (𝟙 A) (𝟙 A) (fst B (Δ[0] : SSet.{u})) SSet.ι₀
  rw [hc, ← Category.assoc, joinTensorRight_unit]

/-- 指定cosliceホモトピーを全錐の族へ移すと、両端・図式・元の固定頂点を保つ。 -/
@[cite HTT "5.1.5.6" (partial := special) "cosliceのuncurryによる局所錐比較の境界の法則。"]
lemma exists_cosliceHomotopyConePrism {A C D : SSet.{u}} (v : C _⦋0⦌)
    {f g : A ⟶ sliceUnder (SSet.yonedaEquiv.symm v)} (H : SSet.Homotopy f g)
    (G : C ⟶ D) :
    ∃ Q : join (Δ[0] : SSet.{u}) A ⊗ (Δ[1] : SSet.{u}) ⟶ D,
      SSet.ι₀ ≫ Q = sliceUnderUncurry f ≫ G ∧
      SSet.ι₁ ≫ Q = sliceUnderUncurry g ≫ G ∧
      (joinInr (Δ[0] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫ Q =
        H.h ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G ∧
      (joinInl (Δ[0] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫ Q =
        fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm v ≫ G := by
  let Q := joinTensorRight (Δ[0] : SSet.{u}) A (Δ[1] : SSet.{u}) ≫
    sliceUnderUncurry H.h ≫ G
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · dsimp only [Q]
    rw [← Category.assoc, joinTensorRight_zero, ← Category.assoc,
      ← sliceUnderUncurry_precomp, H.h₀]
  · dsimp only [Q]
    rw [← Category.assoc, joinTensorRight_ι₁, ← Category.assoc,
      ← sliceUnderUncurry_precomp, H.h₁]
  · dsimp only [Q]
    rw [← Category.assoc, joinTensorRight_inr, ← Category.assoc,
      sliceUnderUncurry_projection]
    exact Category.assoc _ _ _
  · dsimp only [Q]
    rw [← Category.assoc, joinTensorRight_inl, Category.assoc,
      ← Category.assoc (joinInl _ _), sliceUnderUncurry_fixed]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
