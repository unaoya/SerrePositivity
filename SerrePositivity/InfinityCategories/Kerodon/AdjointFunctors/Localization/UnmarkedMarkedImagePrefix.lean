module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFactorWordActionFunctors
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedPrefixHammock
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagReflection

/-!
# 語の圧縮後の元の指定 prefix の W-hammock

概要：像の最小列の prefix を元の指定部分圏へ持ち上げ、元の語の作用と照合する。
方針：最小列の像の等式と包含後の全関手の比較を元の持ち上げで反映する。
規約：指定部分圏の実際の全関手と元の全行・全縦射を保持する。
使われ方：指定因子の W-hammock 余極限の標準射の像の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [])

lemma prefix_arrow_mem_of_first (i : Fin w.length) (hi : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
    (hi0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1))
    (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord w i).length) :
    W.paths (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i hi0).obj d).arrow k) := by
  cases hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.arrow_mem W τ h d k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) ≠ [])

include hT in
lemma imagePrefix_arrow_mem (d : Fin (n.unop.len + 1))
    (k : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))).length) :
    W.paths (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT).obj d).arrow k) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_arrow_mem_of_first W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    ⟨f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h), hT⟩ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_wordAction W f (τ.obj 0) h ⟨_, hT⟩).symm hT d k

def markedImagePrefixFunctor := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W.paths
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixFunctor W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT) (imagePrefix_arrow_mem W f τ h hT)

include hT in
lemma marked_prefix_functor_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedFunctor W τ h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedImagePrefixFunctor W f τ h hT) := by
  let fp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h)
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)))
    (X := (⟨X⟩ : WideSubcategory W.paths))
    (Y := (⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).left⟩ : WideSubcategory W.paths))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedFunctor W τ h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor fp) ⋙ I =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor fp := by
    rw [Functor.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_functor_eq, ← Functor.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedFunctor_inclusion]
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor_inclusion W.paths
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixFunctor W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h)) hT) (imagePrefix_arrow_mem W f τ h hT)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_heq_of_inclusion W.paths rfl rfl
    (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT)).symm _ _
    ((heq_of_eq he).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_functor_heq W f τ h hT).trans (heq_of_eq hr).symm))

include hT in
lemma marked_prefix_functor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedFunctor W τ h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h)) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointChange.functor rfl
        (congrArg (fun Z : Paths C => (⟨Z⟩ : WideSubcategory W.paths))
          (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
            (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT)).symm) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedImagePrefixFunctor W f τ h hT :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.comp_eq_of_heq rfl _ _ _ (marked_prefix_functor_heq W f τ h hT)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
