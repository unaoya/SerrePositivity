module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TensorSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage

/-!
概要：二項積の反映模型に必要な固定頂点の小ささと filtered 保存を構成する。
方針：元の二射影による写像の検出と、指定余錐の成分判定を使う。
規約：元の単体と全余錐を保持する。
使われ方：presentable 圏の二項積の accessibility。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：二項積の固定頂点写像は両成分の固定頂点写像が小さければ小さい。
方針：元の二射影への合成で小さい二型の積へ単射を作る。
規約：標的の充填性を要求しない。使われ方：積の小さい全部分生成模型。 -/
lemma tensor_hasSmallFixedVertexMaps {X Y : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps X) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (X ⊗ Y) := by
  intro A hA v
  let T := {f : A ⟶ X ⊗ Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}
  let TX := {f : A ⟶ X // ∀ a, f.app (Opposite.op ⦋0⦌) a = (v a).1}
  let TY := {f : A ⟶ Y // ∀ a, f.app (Opposite.op ⦋0⦌) a = (v a).2}
  have : Small.{u} TX := hX A hA (fun a ↦ (v a).1)
  have : Small.{u} TY := hY A hA (fun a ↦ (v a).2)
  let code : T → TX × TY := fun f ↦
    (⟨f.val ≫ fst X Y, fun a ↦ congrArg Prod.fst (f.property a)⟩,
      ⟨f.val ≫ snd X Y, fun a ↦ congrArg Prod.snd (f.property a)⟩)
  apply small_of_injective (f := code)
  intro f g h
  apply Subtype.ext
  apply CartesianMonoidalCategory.hom_ext
  · exact congrArg (fun t : TX × TY ↦ t.1.val) h
  · exact congrArg (fun t : TX × TY ↦ t.2.val) h

/-- 概要：同じ κ の filtered 保存関手の二項積は同じ保存性を持つ。
方針：始域の指定余極限を各射影で保存し、標的の成分判定へ渡す。
規約：同じ小さい κ-filtered 全図式を使う。
使われ方：反映の右随伴の二項積の accessibility。 -/
lemma tensorHom_isKappaAccessible {κ : Cardinal.{u}} {C D E F : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] [Quasicategory F]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hF : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits F)
    {f : C ⟶ E} {g : D ⟶ F}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (f ⊗ₘ g) := by
  intro I hI hκ H c hc
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensor_isColimitCone_iff_components hC hD c).mp hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.tensor_isColimitCone_iff_components hE hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (f ⊗ₘ g) c)).mpr
  constructor
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc, tensorHom_fst] using
      hf I (H ≫ fst C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (fst C D) c) h.1
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc, tensorHom_snd] using
      hg I (H ≫ snd C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (snd C D) c) h.2

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
