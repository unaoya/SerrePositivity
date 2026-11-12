module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafPresentable
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：小さい底の直和上の前層圏を、元の成分の前層圏の全直積として表示する。
方針：元の各包含による制限と、単体のラベルごとの関手の貼り合わせを逆同型にする。
規約：同じ指定宇宙変更と全高次自然変換を保持する。
使われ方：presentable 圏の積の前層模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：直和上の元の前層を全ての元の成分へ制限する。
方針：元の単体を各包含と同じ宇宙変更で送り、元の全関手で評価する。
規約：元の全関手の制限。
使われ方：前層の直積模型の順方向。 -/
def presheafSigmaBaseRestriction {ι : Type u} (C : ι → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSSet C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (C i)) where
  app n := ↾fun f i ↦ {
    app d α := ↾fun x ↦ f.app d α (ULift.up ⟨i, x.down⟩)
    naturality {d e} β α := by
      apply ConcreteCategory.hom_ext
      intro x
      exact congrArg (fun q : ((SSet.uliftFunctor.{u + 1, u}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSSet C).op).obj d ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.obj e ↦
        q (ULift.up ⟨i, x.down⟩)) (f.naturality β α) }
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    apply CategoryTheory.Functor.functorHom_ext
    intro d β
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：元の全成分の前層を、同じ直和の底上の全前層へ貼り合わせる。
方針：各元の単体のラベルを取り、その成分の同じ全関手で評価する。
規約：対象の選択や strict な図式への置換を行わない。
使われ方：前層の直積模型の逆方向。 -/
def presheafSigmaBaseGlue {ι : Type u} (C : ι → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (C i)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSSet C) where
  app n := ↾fun f ↦ {
    app d α := ↾fun x ↦ (f x.down.1).app d α (ULift.up x.down.2)
    naturality {d e} β α := by
      apply ConcreteCategory.hom_ext
      rintro ⟨⟨i, x⟩⟩
      exact congrArg (fun q : ((SSet.uliftFunctor.{u + 1, u}).obj (C i).op).obj d ⟶
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.obj e ↦ q (ULift.up x)) ((f i).naturality β α) }
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro d β
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i, x⟩⟩
    rfl

/-- 概要：直和上の元の全前層圏は全成分の前層圏の直積と同型。
方針：元の単体をラベルで制限して貼り戻す二つの恒等式を使う。
規約：元の全関手圏の厳密な同型。
使われ方：小さい前層圏の積の presentable 性。 -/
def presheafSigmaBaseIso {ι : Type u} (C : ι → SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSSet C) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (C i)) where
  hom := presheafSigmaBaseRestriction C
  inv := presheafSigmaBaseGlue C
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨i, x⟩⟩
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

/-- 概要：小さい ∞ 圏上の前層圏の小さい族の元の直積は presentable。
方針：同じ小さい直和の底上の前層圏から指定全同型で移す。
規約：添字の有限性や交換定理の存在入力を課さない。
使われ方：presentable 圏の積の反映模型の始域。 -/
lemma piPresheaf_isPresentable {ι : Type u} (C : ι → SSet.{u})
    [∀ i, Quasicategory (C i)] : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet (fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity (C i))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheaf_isPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSSet C)).of_equivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (presheafSigmaBaseIso C))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
