module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafSigmaBase
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TensorSmallColimits

/-!
概要：二つの前層圏の元の二項積は presentable。
方針：二点で添字付けた前層の直積を元の二項積へ厳密に比較する。
規約：全高次自然変換を保持する。
使われ方：一般 presentable 圏の二項積の反映模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor

/-- 概要：成分ごとの厳密な同型は元の全直積の同型を定める。
方針：各次数の成分へ指定同型を適用する。
規約：同じ小さい添字を使う。使われ方：二項積模型の比較。 -/
def piSSetIso {ι : Type u} {C D : ι → SSet.{u + 1}} (e : ∀ i, C i ≅ D i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet D where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetLift (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i ≫ (e i).hom)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetLift (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection D i ≫ (e i).inv)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    exact congrArg (fun q : C i ⟶ C i ↦ q.app n (f i)) (e i).hom_inv_id
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    exact congrArg (fun q : D i ⟶ D i ↦ q.app n (f i)) (e i).inv_hom_id

/-- 概要：二点上の全直積は元の二項積と同型。
方針：真と偽で評価し、元の対を場合分けで戻す。
規約：添字を宇宙 u に取る。使われ方：前層の二項積。 -/
def piBoolTensorIso (X Y : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet (fun i : ULift.{u} Bool ↦ if i.down then X else Y) ≅ X ⊗ Y where
  hom := {
    app _ := ↾fun f ↦ (f ⟨true⟩, f ⟨false⟩)
    naturality _ _ _ := rfl }
  inv := {
    app _ := ↾fun p i ↦ match i with
      | ⟨true⟩ => p.1
      | ⟨false⟩ => p.2
    naturality _ _ _ := by
      apply ConcreteCategory.hom_ext
      intro p
      funext i
      rcases i with ⟨_ | _⟩ <;> rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    rcases i with ⟨_ | _⟩ <;> rfl
  inv_hom_id := rfl

/-- 概要：二つの小さい ∞ 圏上の前層圏の元の二項積は presentable。
方針：二点で添字付けた小さい前層圏族の presentable 性を全同型で移す。
規約：交換定理や宇宙反映の追加入力を使わない。
使われ方：presentable 圏の二項積の反映の始域。 -/
lemma presheafTensor_isPresentable (A B : SSet.{u}) [Quasicategory A] [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity B) := by
  let C : ULift.{u} Bool → SSet.{u} := fun i ↦ if i.down then A else B
  have : ∀ i, Quasicategory (C i) := by
    rintro ⟨_ | _⟩ <;> dsimp [C] <;> infer_instance
  let e : ∀ i : ULift.{u} Bool,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (C i) ≅ if i.down then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity B := by
    rintro ⟨_ | _⟩ <;> exact Iso.refl _
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity B)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piPresheaf_isPresentable C).of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (piSSetIso e ≪≫ piBoolTensorIso _ _))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
