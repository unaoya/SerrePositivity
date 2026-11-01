module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedZigzagTransport
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeWordAction

/-!
# 元の指定部分圏への持ち上げによる全関手の回収

概要：元の指定部分圏の全 zigzag 関手は、包含して持ち上げ直すと厳密に戻る。
方針：元の全対象・全射の定義と所属証明の一意性を使う。
規約：指定部分圏と元の包含を使う。
使われ方：指定 prefix の語の作用と実際の W-hammock の比較。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.MarkedZigzag
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  (W : MorphismProperty C) [W.IsMultiplicative] {w : Word} {X Y : C}

lemma liftFunctor_reflection
    (F : D ⥤ Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩) :
    liftFunctor W (F ⋙ Zigzag.Relative.functor (inclusion W))
      (fun d j => ((F.obj d).arrow j).property) = F := rfl


lemma functor_heq_of_inclusion {w' : Word} {X' Y' : C}
    (hw : w = w') (hX : X = X') (hY : Y = Y')
    (F : D ⥤ Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w ⟨X⟩ ⟨Y⟩)
    (G : D ⥤ Zigzag (⊤ : MorphismProperty (WideSubcategory W)) w' ⟨X'⟩ ⟨Y'⟩)
    (hFG : HEq (F ⋙ Zigzag.Relative.functor (inclusion W))
      (G ⋙ Zigzag.Relative.functor (inclusion W))) : HEq F G :=
  (heq_of_eq (liftFunctor_reflection W F)).symm.trans
    ((liftFunctor_heq W hw hX hY _ _ (fun d j => ((F.obj d).arrow j).property)
      (fun d j => ((G.obj d).arrow j).property) hFG).trans
      (heq_of_eq (liftFunctor_reflection W G)))

end SerrePositivity.EInfinity.Hammock.MarkedZigzag
