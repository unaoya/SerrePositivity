module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinOpposite
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRightShiftPrism
public import SerrePositivity.InfinityCategories.F1.RelativeJoinCylinder

/-!
概要：左右の relative join の標準指定変換の反転による交換。
方針：join の対角の反転と、二つの pullback 射影で比較する。
規約：左 prism の時間は第一因子、右 prism は第二因子。
使われ方：右指定自然変換の相対 join 表示の円柱部分の両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した左 prism は反対側の標準右 prism と一致する。
方針：両射影で反転を後合成へ分配し、対角の反転と自然性を使う。
規約：右辺では時間の因子を braiding で入れ替える。
使われ方：元の指定変換と右相対 join 表示の標準変換の比較。 -/
lemma kanRelativeJoinPrism_reverse {K C : SSet.{u}} (δ : K ⟶ C) :
    reversePrism (relativeJoinPrism δ) ≫ (kanRelativeJoinOppositeIso δ (𝟙 C)).hom =
      (β_ (Δ[1] : SSet.{u}) K.op).hom ≫
        kanRelativeJoinRightPrism (SSet.opFunctor.map δ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinOppositeIso_fst, ← Category.assoc,
      ← reversePrism_postcomp]
    simp only [relativeJoinPrism, pullback.lift_fst]
    rw [reversePrism_postcomp, Category.assoc, stableJoinReverse_naturality,
      ← Category.assoc, kanJoinDiagonal_reverse]
    change joinDiagonal K.op ≫ joinMap (SSet.opFunctor.map δ) (𝟙 K.op) =
      (β_ (Δ[1] : SSet.{u}) K.op).hom ≫ kanRelativeJoinRightPrism (SSet.opFunctor.map δ) ≫
        pullback.fst (joinMap (𝟙 C.op) (SSet.opFunctor.map δ)) (joinDiagonal C.op)
    simp only [kanRelativeJoinRightPrism, pullback.lift_fst]
    rfl
  · rw [Category.assoc, kanRelativeJoinOppositeIso_snd, ← Category.assoc,
      ← reversePrism_postcomp]
    simp only [relativeJoinPrism, pullback.lift_snd]
    change reversePrism ((Δ[1] : SSet.{u}) ◁ δ) ≫ (kanPrismOppositeIso C).hom =
      (β_ (Δ[1] : SSet.{u}) K.op).hom ≫ kanRelativeJoinRightPrism (SSet.opFunctor.map δ) ≫
        pullback.snd (joinMap (𝟙 C.op) (SSet.opFunctor.map δ)) (joinDiagonal C.op)
    simp only [kanRelativeJoinRightPrism, pullback.lift_snd]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, a⟩
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      change ((t i.rev.rev).rev).rev = t i
      simp
    · rfl

/-- 概要：反転した右標準 prism は反対側の左標準 prism に一致する。
方針：左右を交換した対角の反転を、二つの pullback 射影で計算する。
規約：右 prism の時間を第一因子へ直してから反転する。
使われ方：右円柱比較の prism 部分の同定。 -/
lemma kanRelativeJoinRightPrism_reverse {K C : SSet.{u}} (δ : K ⟶ C) :
    reversePrism ((β_ (Δ[1] : SSet.{u}) K).hom ≫ kanRelativeJoinRightPrism δ) ≫
      (kanRelativeJoinOppositeIso (𝟙 C) δ).hom =
      relativeJoinPrism (SSet.opFunctor.map δ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinOppositeIso_fst, ← Category.assoc,
      ← reversePrism_postcomp]
    simp only [Category.assoc, kanRelativeJoinRightPrism, pullback.lift_fst]
    change reversePrism (joinDiagonal K ≫ joinMap δ (𝟙 K)) ≫
      (stableJoinReverseIso C K).hom =
      relativeJoinPrism (SSet.opFunctor.map δ) ≫
        pullback.fst (joinMap (SSet.opFunctor.map δ) (𝟙 C.op)) (joinDiagonal C.op)
    rw [reversePrism_postcomp, Category.assoc, stableJoinReverse_naturality,
      ← Category.assoc, kanJoinDiagonal_reverse]
    simp only [relativeJoinPrism, pullback.lift_fst, CategoryTheory.Functor.map_id]
  · rw [Category.assoc, kanRelativeJoinOppositeIso_snd, ← Category.assoc,
      ← reversePrism_postcomp]
    simp only [Category.assoc, kanRelativeJoinRightPrism, pullback.lift_snd]
    change reversePrism ((Δ[1] : SSet.{u}) ◁ δ) ≫ (kanPrismOppositeIso C).hom =
      relativeJoinPrism (SSet.opFunctor.map δ) ≫
        pullback.snd (joinMap (SSet.opFunctor.map δ) (𝟙 C.op)) (joinDiagonal C.op)
    simp only [relativeJoinPrism, pullback.lift_snd]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, a⟩
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      change ((t i.rev.rev).rev).rev = t i
      simp
    · rfl

end SerrePositivity.InfinityCategories
