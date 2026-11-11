module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiFunctorMap
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleReflectiveImage

/-!
概要：小さい全直積の反映模型に必要な固定頂点写像の小ささと filtered 保存。
方針：指定射影による写像の検出と元の余錐の成分判定を使う。
規約：元の濃度と小さい添字を保持する。
使われ方：小さい積の accessibility の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい全直積は各成分の固定頂点写像の小ささを受け継ぐ。
方針：全写像を各成分の固定頂点写像の小さい全直積へ単射に送る。
規約：成分の充填性を要求しない。
使われ方：直積の小さい全部分生成模型。 -/
lemma piSSet_hasSmallFixedVertexMaps {ι : Type u} {C : ι → SSet.{u + 1}}
    (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (C i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) := by
  intro A hA v
  let T (i : ι) := {f : A ⟶ C i // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a i}
  have (i : ι) : Small.{u} (T i) := hC i A hA (fun a ↦ v a i)
  let code (f : {f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}) :
      ∀ i, T i := fun i ↦ ⟨f.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i,
        fun a ↦ congrFun (f.property a) i⟩
  apply small_of_injective (f := code)
  intro f g h
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_hom_ext
  intro i
  exact congrArg (fun t : ∀ i, T i ↦ (t i).val) h

/-- 概要：同じ κ の filtered 保存関手の小さい全直積は同じ保存性を持つ。
方針：元の指定余錐を全成分に送り、各成分の保存から元の像の普遍性を得る。
規約：余完備性と同じ κ を明示する。
使われ方：直積反映の包含の accessibility。 -/
lemma piSSetMap_isKappaAccessible {ι : Type u} {κ : Cardinal.{u}}
    {C D : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)] [∀ i, Quasicategory (D i)]
    (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (C i)) (hD : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (D i))
    {f : ∀ i, C i ⟶ D i} (hf : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (f i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap f) := by
  intro I hI hκ H c hc
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isColimitCone_iff_components hC c).mp hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isColimitCone_iff_components hD (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap f) c)).mpr
  intro i
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetMap_projection] using
    hf i I (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) c) (h i)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
