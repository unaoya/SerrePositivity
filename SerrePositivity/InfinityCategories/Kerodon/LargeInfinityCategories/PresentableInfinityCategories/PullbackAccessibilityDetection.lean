module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FixedVertexMapSmallness

/-!
概要：引き戻しの固定頂点写像の小ささと filtered 保存の成分判定。
方針：元の両射影の共同単射性と指定余錐の成分判定を利用する。
規約：引き戻しの accessibility 自体を入力や結論へ隠さない。
使われ方：Pr^L の引き戻しの小さい生成模型の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：引き戻しは両始域の固定頂点写像の小ささを受け継ぐ。
方針：元の写像を両射影の小さい固定頂点写像型の積へ単射に送る。
規約：充填性や余極限の存在は要求しない。
使われ方：引き戻し内の対象族の小さい全部分模型。 -/
lemma pullback_hasSmallFixedVertexMaps {E D B : SSet.{u + 1}}
    (p : E ⟶ B) (q : D ⟶ B)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (pullback p q) := by
  intro A hA v
  let ve := fun a ↦ (pullback.fst p q).app (Opposite.op ⦋0⦌) (v a)
  let vd := fun a ↦ (pullback.snd p q).app (Opposite.op ⦋0⦌) (v a)
  let TE := {f : A ⟶ E // ∀ a, f.app (Opposite.op ⦋0⦌) a = ve a}
  let TD := {f : A ⟶ D // ∀ a, f.app (Opposite.op ⦋0⦌) a = vd a}
  have : Small.{u} TE := hE A hA ve
  have : Small.{u} TD := hD A hA vd
  let code (f : {f : A ⟶ pullback p q // ∀ a, f.app (Opposite.op ⦋0⦌) a = v a}) :
      TE × TD :=
    (⟨f.val ≫ pullback.fst p q,
        fun a ↦ congrArg ((pullback.fst p q).app (Opposite.op ⦋0⦌)) (f.property a)⟩,
      ⟨f.val ≫ pullback.snd p q,
        fun a ↦ congrArg ((pullback.snd p q).app (Opposite.op ⦋0⦌)) (f.property a)⟩)
  apply small_of_injective (f := code)
  intro f g h
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg (fun t : TE × TD ↦ t.1.val) h
  · exact congrArg (fun t : TE × TD ↦ t.2.val) h

/-- 概要：引き戻しへの関手の κ-filtered 保存を両成分で判定する。
方針：元の指定余錐の像を両成分へ送り、同じ引き戻し内の成分判定で戻す。
規約：両構造関手の小余極限保存と一方の同値持ち上げを明示する。
使われ方：引き戻しの反映模型の包含の filtered 保存。 -/
lemma pullback_isKappaAccessibleFunctor_of_components {κ : Cardinal.{u}}
    {E D B X : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)
    (G : X ⟶ pullback p q)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (G ≫ pullback.fst p q))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (G ≫ pullback.snd p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G := by
  intro I hI hκ H c hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_isColimitCone_iff_components p q hp hE hD hpc hqc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)).mpr
  constructor
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using he I H c hc
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hd I H c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
