module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackLift
/-!
概要：厳密に可換な三成分の cospan 比較は、元の矢印族と二入力を保つ lax pullback 比較を誘導する。
方針：矢印の後合成と両入力の積を元の引き戻しへ適用する。
規約：三成分と二可換条件を変更しない。使われ方：元二脚の全比較の輸送。

対応節は Kerodon 5.5（Tag 01YV）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

lemma arrowEndpointPair_post {C C' : SSet.{u}} (c : C ⟶ C') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C ≫ (c ⊗ₘ c) = (ihom (Δ[1] : SSet.{u})).map c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair C' := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

variable {A B C A' B' C' : SSet.{u}}
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hp : p ≫ c = a ≫ p') (hq : q ≫ c = b ≫ q')

include hp hq in
lemma laxPullbackCospanMap_inputs_condition :
    (p ⊗ₘ q) ≫ (c ⊗ₘ c) = (a ⊗ₘ b) ≫ (p' ⊗ₘ q') := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hp, hq]

def laxPullbackCospanMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p' q' :=
  pullback.map _ _ _ _ ((ihom (Δ[1] : SSet.{u})).map c) (a ⊗ₘ b) (c ⊗ₘ c)
    (arrowEndpointPair_post c) (laxPullbackCospanMap_inputs_condition p q p' q' a b c hp hq)

lemma laxPullbackCospanMap_arrow :
    laxPullbackCospanMap p q p' q' a b c hp hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p' q' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q ≫ (ihom (Δ[1] : SSet.{u})).map c := pullback.lift_fst _ _ _

lemma laxPullbackCospanMap_inputs :
    laxPullbackCospanMap p q p' q' a b c hp hq ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (a ⊗ₘ b) := pullback.lift_snd _ _ _

lemma laxPullbackCospanMap_fst :
    laxPullbackCospanMap p q p' q' a b c hp hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p' q' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q ≫ a := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst, ← Category.assoc, laxPullbackCospanMap_inputs,
    Category.assoc, tensorHom_fst]
  rfl

lemma laxPullbackCospanMap_snd :
    laxPullbackCospanMap p q p' q' a b c hp hq ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p' q' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q ≫ b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd, ← Category.assoc, laxPullbackCospanMap_inputs,
    Category.assoc, tensorHom_snd]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
