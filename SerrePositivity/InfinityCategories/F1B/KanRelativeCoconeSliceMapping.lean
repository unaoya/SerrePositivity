module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeFamilyInitial
public import SerrePositivity.InfinityCategories.Stable.CosliceCoconeFamilyEquivalence

/-!
概要：相対余錐の充填条件から通常の coslice の写像空間の普遍性を回収する。
方針：coslice と図式固定の余錐の族の比較の自然性で写像空間の同値を移す。
規約：U に fibration 性は不要。
使われ方：操作的な相対余錐条件から標準的な U 余極限への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：coslice と余錐の族の比較は値域の後合成に自然。
方針：fiber の包含へ合成し、普遍余錐の uncurry の後合成公式を使う。
規約：図式の始域と二つの値域は任意。
使われ方：固定図式の二つの余錐圏の写像空間の比較。 -/
lemma kanCosliceCoconeFamilyMap_postcomp {K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) :
    cosliceCoconeFamilyMap p ≫ kanCoconeFamilyPostcomp p U =
      sliceUnderPostcomp p U ≫ cosliceCoconeFamilyMap (p ≫ U) := by
  apply vertexFiber_hom_ext (coconeRestriction K E) (functorVertex (p ≫ U))
  rw [Category.assoc]
  change cosliceCoconeFamilyMap p ≫
      (vertexFiberι (coconeRestriction K D) (functorVertex p) ≫
        (ihom (join K (Δ[0] : SSet.{u}))).map U) = _
  change curry (cosliceCoconeFamilyUncurry p) ≫
      (ihom (join K (Δ[0] : SSet.{u}))).map U =
    sliceUnderPostcomp p U ≫ curry (cosliceCoconeFamilyUncurry (p ≫ U))
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_left, uncurry_curry, uncurry_curry]
  unfold cosliceCoconeFamilyUncurry
  simp only [Category.assoc]
  rw [← Category.assoc (join K (Δ[0] : SSet.{u}) ◁ sliceUnderPostcomp p U),
    stable_joinTensorRight_naturality]
  simp only [Category.assoc]
  have hn : ((Δ[0] : SSet.{u}) ◁ sliceUnderPostcomp p U) ≫
      CartesianMonoidalCategory.snd Δ[0] (sliceUnder (p ≫ U)) =
    CartesianMonoidalCategory.snd Δ[0] (sliceUnder p) ≫ sliceUnderPostcomp p U := rfl
  have hj : joinMap (𝟙 K) ((Δ[0] : SSet.{u}) ◁ sliceUnderPostcomp p U) ≫
      joinMap (𝟙 K) (CartesianMonoidalCategory.snd Δ[0] (sliceUnder (p ≫ U))) =
    joinMap (𝟙 K) (CartesianMonoidalCategory.snd Δ[0] (sliceUnder p)) ≫
      joinMap (𝟙 K) (sliceUnderPostcomp p U) := by
    rw [← joinMap_comp, ← joinMap_comp, hn]
  rw [← Category.assoc
    (joinMap (𝟙 K) ((Δ[0] : SSet.{u}) ◁ sliceUnderPostcomp p U))
    (joinMap (𝟙 K) (CartesianMonoidalCategory.snd Δ[0] (sliceUnder (p ≫ U)))), hj]
  simp only [Category.assoc]
  rw [← sliceUnderUncurry_precomp, Category.comp_id]
  have hu := sliceUnderUncurry_postcomp (𝟙 (sliceUnder p)) U
  simp only [Category.id_comp] at hu
  rw [hu]

/-- 概要：相対余錐の充填条件は通常の coslice の全ての指定終点への写像空間を保つ。
方針：余錐の族での同値を coslice 比較の充満忠実性と自然性で挟む。
規約：元の余錐 c と標的余錐 d を明示し、U の充填性は要求しない。
使われ方：標準的な U 余極限の相対始対象による判定。 -/
lemma kanRelativeCoconeLifting_slice_pinchedHom_equivalence {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (p : K ⟶ D) (U : D ⟶ E)
    (c : JoinCocone p) (hc : KanRelativeCoconeLifting U c) (d : JoinCocone p) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap (sliceUnderPostcomp p U) c d) := by
  have hx := kanCoconeFamilyPostcomp_initialBoundary p U c hc
  rw [← cosliceCoconeFamilyMap_app_zero p c] at hx
  have hb := kanPinchedHomMap_equivalence_of_initialBoundary (kanCoconeFamilyPostcomp p U)
    _ ((cosliceCoconeFamilyMap p).app (Opposite.op ⦋0⦌) d) hx
  have he := ((isQCatEquivalence_cosliceCoconeFamilyMap p).isFullyFaithful c d).comp hb
  rw [← pinchedHomMap_comp] at he
  have hnat := congrArg
    (fun f : sliceUnder p ⟶ coconeFamily (p ≫ U) ↦
      IsSimplicialHomotopyEquivalence (pinchedHomMap f c d))
    (kanCosliceCoconeFamilyMap_postcomp p U)
  have he' := hnat.mp he
  rw [pinchedHomMap_comp] at he'
  exact ((isQCatEquivalence_cosliceCoconeFamilyMap (p ≫ U)).isFullyFaithful
    _ _).cancel_right he'

end SerrePositivity.InfinityCategories.F1B
