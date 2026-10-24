module
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift

/-! # 固定辺を保つ三角形 prism の合成対応への持ち上げ

概要：貼り合わせ後の全三角形族から、元の入力を保つ実ホモトピーを取り出す。
方針：時間をパラメーターへ含めて同じ合成対応へ持ち上げ、両端を評価で同定する。
規約：固定辺と可変入力の全時間の等式を要求し、端点一致だけで代用しない。
使われ方：側面補正済みの prism を選択済み変形との相対比較へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：入力を全時間で固定するホモトピーを、入力付き引き戻しへ持ち上げる。
方針：円柱上で引き戻しの普遍性を使い、同じ二射影で両端を同定する。
規約：基底の一致は円柱全体で要求する。使われ方：左右の元 Hom 入力の保持。 -/
def dgGluingFixedInputPullbackHomotopy {K E B Z : SSet.{u}}
    (p : E ⟶ Z) (q : B ⟶ Z) {L₀ L₁ : K ⟶ E} (H : SSet.Homotopy L₀ L₁)
    (a : K ⟶ B) (ha₀ : L₀ ≫ p = a ≫ q) (ha₁ : L₁ ≫ p = a ≫ q)
    (hp : H.h ≫ p = (fst K (Δ[1] : SSet.{u}) ≫ a) ≫ q) :
    SSet.Homotopy (pullback.lift L₀ a ha₀) (pullback.lift L₁ a ha₁) where
  h := pullback.lift H.h (fst K Δ[1] ≫ a) hp
  h₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, H.h₀]
      exact (pullback.lift_fst L₀ a ha₀).symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ι₀_fst, Category.id_comp]
      exact (pullback.lift_snd L₀ a ha₀).symm
  h₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, H.h₁]
      exact (pullback.lift_fst L₁ a ha₁).symm
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ι₁_fst, Category.id_comp]
      exact (pullback.lift_snd L₁ a ha₁).symm
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro b
    exact False.elim b.1.property

lemma dgGluingFixedInputPullbackHomotopy_over {K E B Z : SSet.{u}}
    (p : E ⟶ Z) (q : B ⟶ Z) {L₀ L₁ : K ⟶ E} (H : SSet.Homotopy L₀ L₁)
    (a : K ⟶ B) (ha₀ : L₀ ≫ p = a ≫ q) (ha₁ : L₁ ≫ p = a ≫ q)
    (hp : H.h ≫ p = (fst K (Δ[1] : SSet.{u}) ≫ a) ≫ q) :
    (dgGluingFixedInputPullbackHomotopy p q H a ha₀ ha₁ hp).h ≫ pullback.snd p q =
      fst K (Δ[1] : SSet.{u}) ≫ a :=
  pullback.lift_snd _ _ _

def dgGluingFirstFixedCompositionTriangleHomotopy {Z K : SSet.{u}}
    {x y : Z _⦋0⦌} (e : Z.Edge x y) (z : Z _⦋0⦌)
    (a : K ⟶ intervalMappingSpace y z)
    (L₀ L₁ : K ⟶ dgGluingFirstFixedCompositionSpace e z)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ V =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ SSet.yonedaEquiv.symm e.edge)
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ V =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{u}) ≫ a))
    (h₀ : (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ V =
      (Δ[2] ◁ L₀) ≫ dgGluingFirstFixedCompositionEvaluation e z)
    (h₁ : (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ V =
      (Δ[2] ◁ L₁) ≫ dgGluingFirstFixedCompositionEvaluation e z)
    (ha₀ : L₀ ≫ dgGluingFirstFixedCompositionSecond e z = a)
    (ha₁ : L₁ ≫ dgGluingFirstFixedCompositionSecond e z = a) : SSet.Homotopy L₀ L₁ where
  h := dgGluingFirstFixedCompositionLift e z (fst K Δ[1] ≫ a) V hfirst hlast
  h₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, dgGluingFirstFixedCompositionLift_triangle,
        ← curry_natural_left, h₀, curry_natural_left]
      simp only [dgGluingFirstFixedCompositionEvaluation, curry_uncurry]
      rfl
    · change ι₀ ≫ (dgGluingFirstFixedCompositionLift e z _ V hfirst hlast ≫
        dgGluingFirstFixedCompositionSecond e z) = L₀ ≫ _
      rw [dgGluingFirstFixedCompositionLift_second, ← Category.assoc,
        ι₀_fst, Category.id_comp]
      exact ha₀.symm
  h₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, dgGluingFirstFixedCompositionLift_triangle,
        ← curry_natural_left, h₁, curry_natural_left]
      simp only [dgGluingFirstFixedCompositionEvaluation, curry_uncurry]
      rfl
    · change ι₁ ≫ (dgGluingFirstFixedCompositionLift e z _ V hfirst hlast ≫
        dgGluingFirstFixedCompositionSecond e z) = L₁ ≫ _
      rw [dgGluingFirstFixedCompositionLift_second, ← Category.assoc,
        ι₁_fst, Category.id_comp]
      exact ha₁.symm
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

def dgGluingLastFixedCompositionTriangleHomotopy {Z K : SSet.{u}}
    (x : Z _⦋0⦌) {y z : Z _⦋0⦌} (e : Z.Edge y z)
    (a : K ⟶ intervalMappingSpace x y)
    (L₀ L₁ : K ⟶ compositionCorrespondence x e)
    (V : (Δ[2] : SSet.{u}) ⊗ (K ⊗ Δ[1]) ⟶ Z)
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ V =
      intervalMappingUncurry (fst K (Δ[1] : SSet.{u}) ≫ a))
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ (K ⊗ Δ[1])) ≫ V =
      fst (Δ[1] : SSet.{u}) (K ⊗ Δ[1]) ≫ SSet.yonedaEquiv.symm e.edge)
    (h₀ : (Δ[2] ◁ (ι₀ : K ⟶ _)) ≫ V =
      (Δ[2] ◁ L₀) ≫ compositionCorrespondenceEvaluation x e)
    (h₁ : (Δ[2] ◁ (ι₁ : K ⟶ _)) ≫ V =
      (Δ[2] ◁ L₁) ≫ compositionCorrespondenceEvaluation x e)
    (ha₀ : L₀ ≫ compositionCorrespondenceFirst x e = a)
    (ha₁ : L₁ ≫ compositionCorrespondenceFirst x e = a) : SSet.Homotopy L₀ L₁ where
  h := dgGluingLastFixedCompositionLift x e (fst K Δ[1] ≫ a) V hfirst hlast
  h₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, dgGluingLastFixedCompositionLift_triangle,
        ← curry_natural_left, h₀, curry_natural_left]
      simp only [compositionCorrespondenceEvaluation, curry_uncurry]
      rfl
    · change ι₀ ≫ (dgGluingLastFixedCompositionLift x e _ V hfirst hlast ≫
        compositionCorrespondenceFirst x e) = L₀ ≫ _
      rw [dgGluingLastFixedCompositionLift_first, ← Category.assoc,
        ι₀_fst, Category.id_comp]
      exact ha₀.symm
  h₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, dgGluingLastFixedCompositionLift_triangle,
        ← curry_natural_left, h₁, curry_natural_left]
      simp only [compositionCorrespondenceEvaluation, curry_uncurry]
      rfl
    · change ι₁ ≫ (dgGluingLastFixedCompositionLift x e _ V hfirst hlast ≫
        compositionCorrespondenceFirst x e) = L₁ ≫ _
      rw [dgGluingLastFixedCompositionLift_first, ← Category.assoc,
        ι₁_fst, Category.id_comp]
      exact ha₁.symm
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories
