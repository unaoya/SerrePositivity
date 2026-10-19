module

public import SerrePositivity.InfinityCategories.F1.SpanPullbackLifting
public import SerrePositivity.InfinityCategories.F1B.IntervalFamilyPathParameters

/-!
概要：三対象の span の可逆 path 置換と、指定した元の比較の回収。
方針：始点比較の二射影を交換し、標準切断の自然性を用いる。
規約：元の span と全ての可換等式を保持する。
使われ方：同値な局所化比較の pullback による貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- span の相対比較に合わせ、始点比較の二つの射影を交換する。 -/
def replacementSquareStartCornerFlipped {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    equivalencePathReplacement u ⟶ pullback p (equivalencePathReplacementProjection v) :=
  replacementSquareStartCorner u v p q h ≫
    (pullbackSymmetry (equivalencePathReplacementProjection v) p).hom

/-- 交換した始点比較の第一射影は元の始域への射影。 -/
lemma replacementSquareStartCornerFlipped_fst {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareStartCornerFlipped u v p q h ≫
        pullback.fst p (equivalencePathReplacementProjection v) =
      equivalencePathReplacementProjection u := by
  rw [replacementSquareStartCornerFlipped, Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullback.lift_snd _ _ _

/-- 交換した始点比較の第二射影は四角形の同時解像。 -/
lemma replacementSquareStartCornerFlipped_snd {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    replacementSquareStartCornerFlipped u v p q h ≫
        pullback.snd p (equivalencePathReplacementProjection v) =
      replacementSquareMap u v p q h := by
  rw [replacementSquareStartCornerFlipped, Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

/-- 始点比較の全境界持ち上げは、二つの射影を交換しても保たれる。 -/
instance replacementSquareStartCornerFlipped_trivialKanFibration {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v)
    [TrivialKanFibration (relativeEquivalencePathMapAt q 0)] :
    TrivialKanFibration (replacementSquareStartCornerFlipped u v p q h) := by
  exact ⟨trivialKanFibrations.comp_mem _ _
    (TrivialKanFibration.mem (p := replacementSquareStartCorner u v p q h))
    (TrivialKanFibration.mem (p :=
      (pullbackSymmetry (equivalencePathReplacementProjection v) p).hom))⟩

/-- 可逆 path 置換の標準切断は、元の可換四角形に厳密に自然。 -/
lemma replacementSquareMap_section {A B X Y : SSet.{u}}
    (u : A ⟶ X) (v : B ⟶ Y) (p : A ⟶ B) (q : X ⟶ Y) (h : u ≫ q = p ≫ v) :
    equivalencePathReplacementSection u ≫ replacementSquareMap u v p q h =
      p ≫ equivalencePathReplacementSection v := by
  have hf : replacementSquareMap u v p q h ≫ pullback.fst (equivalencePathEndpoint Y 0) v =
      pullback.fst (equivalencePathEndpoint X 0) u ≫ equivalencePathMap q :=
    relativePathSquareTargetMap_fst u v p q h 0
  apply pullback.hom_ext
  · rw [Category.assoc]
    change equivalencePathReplacementSection u ≫
      (replacementSquareMap u v p q h ≫ pullback.fst (equivalencePathEndpoint Y 0) v) = _
    rw [hf]
    change equivalencePathReplacementSection u ≫
        (pullback.fst (equivalencePathEndpoint X 0) u ≫ equivalencePathMap q) = _
    rw [← Category.assoc]
    rw [show equivalencePathReplacementSection u ≫
      pullback.fst (equivalencePathEndpoint X 0) u = u ≫ equivalencePathRefl X from
        pullback.lift_fst _ _ _, Category.assoc, equivalencePathRefl_map, ← Category.assoc, h]
    change (p ≫ v) ≫ equivalencePathRefl Y =
      p ≫ (equivalencePathReplacementSection v ≫ pullback.fst (equivalencePathEndpoint Y 0) v)
    rw [show equivalencePathReplacementSection v ≫
      pullback.fst (equivalencePathEndpoint Y 0) v = v ≫ equivalencePathRefl Y from
        pullback.lift_fst _ _ _, Category.assoc]
  · change (equivalencePathReplacementSection u ≫ replacementSquareMap u v p q h) ≫
        equivalencePathReplacementProjection v =
      (p ≫ equivalencePathReplacementSection v) ≫ equivalencePathReplacementProjection v
    rw [Category.assoc, replacementSquareMap_projection, ← Category.assoc,
      equivalencePathReplacementSection_projection, Category.id_comp, Category.assoc,
      equivalencePathReplacementSection_projection, Category.comp_id]

/-- 同時解像の両端の持ち上げにより、同値な span の実際の pullback 比較も同値。 -/
lemma isPrecompositionEquivalence_spanPullbackMap_of_equivalenceLifting
    {A₀ A₁ A₂ B₀ B₁ B₂ : SSet.{u}}
    [Quasicategory A₀] [Quasicategory A₁] [Quasicategory A₂]
    [Quasicategory B₀] [Quasicategory B₁] [Quasicategory B₂]
    (p₁ : A₁ ⟶ A₀) (p₂ : A₂ ⟶ A₀) (q₁ : B₁ ⟶ B₀) (q₂ : B₂ ⟶ B₀)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (u₂ : A₂ ⟶ B₂)
    (h₁ : u₁ ≫ q₁ = p₁ ≫ u₀) (h₂ : u₂ ≫ q₂ = p₂ ≫ u₀)
    (hu₀ : IsQCatEquivalence u₀) (hu₁ : IsQCatEquivalence u₁) (hu₂ : IsQCatEquivalence u₂)
    (hp₁ : F1B.KanEquivalenceLifting p₁) (hq₁ : F1B.KanEquivalenceLifting q₁)
    [TrivialKanFibration (relativeEquivalencePathMapAt q₁ 0)] :
    IsPrecompositionEquivalence (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
  let r₁ := replacementSquareMap u₁ u₀ p₁ q₁ h₁
  let r₂ := replacementSquareMap u₂ u₀ p₂ q₂ h₂
  have hs₁ : equivalencePathReplacementProjection u₁ ≫ p₁ =
      r₁ ≫ equivalencePathReplacementProjection u₀ :=
    (replacementSquareMap_projection u₁ u₀ p₁ q₁ h₁).symm
  have hs₂ : equivalencePathReplacementProjection u₂ ≫ p₂ =
      r₂ ≫ equivalencePathReplacementProjection u₀ :=
    (replacementSquareMap_projection u₂ u₀ p₂ q₂ h₂).symm
  have ht₁ : equivalencePathReplacementMap u₁ ≫ q₁ =
      r₁ ≫ equivalencePathReplacementMap u₀ :=
    (replacementSquareMap_endpoint u₁ u₀ p₁ q₁ h₁).symm
  have ht₂ : equivalencePathReplacementMap u₂ ≫ q₂ =
      r₂ ≫ equivalencePathReplacementMap u₀ :=
    (replacementSquareMap_endpoint u₂ u₀ p₂ q₂ h₂).symm
  let s := spanPullbackMap r₁ r₂ p₁ p₂ (equivalencePathReplacementProjection u₀)
    (equivalencePathReplacementProjection u₁) (equivalencePathReplacementProjection u₂) hs₁ hs₂
  let t := spanPullbackMap r₁ r₂ q₁ q₂ (equivalencePathReplacementMap u₀)
    (equivalencePathReplacementMap u₁) (equivalencePathReplacementMap u₂) ht₁ ht₂
  have hs : TrivialKanFibration s :=
    trivialKanFibration_spanPullbackMap_of_left_corner r₁ r₂ p₁ p₂ _ _ _ hs₁ hs₂
      (replacementSquareStartCornerFlipped u₁ u₀ p₁ q₁ h₁)
      (replacementSquareStartCornerFlipped_fst u₁ u₀ p₁ q₁ h₁)
      (replacementSquareStartCornerFlipped_snd u₁ u₀ p₁ q₁ h₁)
  have := hu₂.equivalencePathReplacementMap_trivialKanFibration
  have := trivialKanFibration_replacementSquareEndCorner u₁ u₀ p₁ q₁ h₁ hu₁ hu₀ hp₁ hq₁
  have ht : TrivialKanFibration t :=
    trivialKanFibration_spanPullbackMap_of_left_corner r₁ r₂ q₁ q₂ _ _ _ ht₁ ht₂
      (replacementSquareEndCorner u₁ u₀ p₁ q₁ h₁)
      (replacementSquareEndCorner_fst u₁ u₀ p₁ q₁ h₁)
      (replacementSquareEndCorner_snd u₁ u₀ p₁ q₁ h₁)
  have hj₁ : equivalencePathReplacementSection u₁ ≫ r₁ =
      p₁ ≫ equivalencePathReplacementSection u₀ :=
    replacementSquareMap_section u₁ u₀ p₁ q₁ h₁
  have hj₂ : equivalencePathReplacementSection u₂ ≫ r₂ =
      p₂ ≫ equivalencePathReplacementSection u₀ :=
    replacementSquareMap_section u₂ u₀ p₂ q₂ h₂
  let j := spanPullbackMap p₁ p₂ r₁ r₂ (equivalencePathReplacementSection u₀)
    (equivalencePathReplacementSection u₁) (equivalencePathReplacementSection u₂) hj₁ hj₂
  have hjs : j ≫ s = 𝟙 (pullback p₁ p₂) := by
    apply pullback.hom_ext
    · dsimp only [j, s]
      rw [Category.assoc, spanPullbackMap_fst, ← Category.assoc, spanPullbackMap_fst,
        Category.assoc, equivalencePathReplacementSection_projection,
        Category.comp_id, Category.id_comp]
    · dsimp only [j, s]
      rw [Category.assoc, spanPullbackMap_snd, ← Category.assoc, spanPullbackMap_snd,
        Category.assoc, equivalencePathReplacementSection_projection,
        Category.comp_id, Category.id_comp]
  have hjt : j ≫ t = spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂ := by
    apply pullback.hom_ext
    · dsimp only [j, t]
      rw [Category.assoc, spanPullbackMap_fst, ← Category.assoc, spanPullbackMap_fst,
        Category.assoc, equivalencePathReplacementSection_map, spanPullbackMap_fst]
    · dsimp only [j, t]
      rw [Category.assoc, spanPullbackMap_snd, ← Category.assoc, spanPullbackMap_snd,
        Category.assoc, equivalencePathReplacementSection_map, spanPullbackMap_snd]
  have := hp₁.innerFibration
  have := hq₁.innerFibration
  have : InnerFibration (pullback.snd p₁ p₂) :=
    ⟨innerFibrations.pullback_snd _ _ (mem_innerFibrations p₁)⟩
  have : InnerFibration (pullback.snd q₁ q₂) :=
    ⟨innerFibrations.pullback_snd _ _ (mem_innerFibrations q₁)⟩
  have : Quasicategory (pullback p₁ p₂) := quasicategory_of_innerFibration (pullback.snd p₁ p₂)
  have : Quasicategory (pullback q₁ q₂) := quasicategory_of_innerFibration (pullback.snd q₁ q₂)
  have : Quasicategory (pullback r₁ r₂) := quasicategory_of_innerFibration s
  have hj : IsQCatEquivalence j := by
    apply (isQCatEquivalence_of_trivialKanFibration s).cancel_right
    rw [hjs]
    exact (QCatEquivalence.refl _).isQCatEquivalence
  have he : IsQCatEquivalence (spanPullbackMap p₁ p₂ q₁ q₂ u₀ u₁ u₂ h₁ h₂) := by
    rw [← hjt]
    exact hj.comp (isQCatEquivalence_of_trivialKanFibration t)
  exact he.isPrecompositionEquivalence

end SerrePositivity.InfinityCategories
