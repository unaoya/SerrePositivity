module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction

/-!
# 元の指定部分圏への持ち上げによる全関手の回収

概要：元の指定部分圏の全 zigzag 関手は、包含して持ち上げ直すと厳密に戻る。
方針：元の全対象・全射の定義と所属証明の一意性を使う。
規約：指定部分圏と元の包含を使う。
使われ方：指定 prefix の語の作用と実際の W-hammock の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma liftFunctor_reflection
    (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W))
      (fun d j => ((F.obj d).arrow j).property) = F := rfl


lemma functor_heq_of_inclusion {w' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X' Y' : C}
    (hw : w = w') (hX : X = X') (hY : Y = Y')
    (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩)
    (G : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w' ⟨X'⟩ ⟨Y'⟩)
    (hFG : HEq (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W))
      (G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W))) : HEq F G :=
  (heq_of_eq (liftFunctor_reflection W F)).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftFunctor_heq W hw hX hY _ _ (fun d j => ((F.obj d).arrow j).property)
      (fun d j => ((G.obj d).arrow j).property) hFG).trans
      (heq_of_eq (liftFunctor_reflection W G)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
