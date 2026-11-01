module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPadding
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# 元の padding 余極限の射の左逆

概要：元の図式から padding 図式の余極限への射は、元の標準射による左逆を持つ。
方針：語の添字を padding へ移した余錐と、元の包含への余錐の自然性を使う。
規約：逆側の合成の恒等性や弱同値性は主張しない。
使われ方：三本矢の比較ホモトピーと弱同値性の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (H : Word ⥤ C)
  [HasColimit H] [HasColimit (Word.paddingFunctor ⋙ H)]

def paddingColimitMap : colimit H ⟶ colimit (Word.paddingFunctor ⋙ H) :=
  colimMap (Functor.whiskerRight Word.paddingInclusionNat H)

def paddingColimitRetraction : colimit (Word.paddingFunctor ⋙ H) ⟶ colimit H :=
  colimit.pre H Word.paddingFunctor

lemma paddingColimitRetraction_fac (a : Word) :
    colimit.ι (Word.paddingFunctor ⋙ H) a ≫ paddingColimitRetraction H =
      colimit.ι H (Word.paddingFunctor.obj a) := colimit.ι_pre H Word.paddingFunctor a

lemma paddingColimitMap_retraction : paddingColimitMap H ≫ paddingColimitRetraction H =
    𝟙 (colimit H) := by
  apply colimit.hom_ext
  intro a
  change colimit.ι H a ≫
    (colimMap (Functor.whiskerRight Word.paddingInclusionNat H) ≫
      paddingColimitRetraction H) = colimit.ι H a ≫ 𝟙 _
  rw [← Category.assoc, ι_colimMap, Category.assoc, paddingColimitRetraction_fac,
    Category.comp_id]
  exact colimit.w H (Word.paddingInclusionNat.app a)

end SerrePositivity.EInfinity.Hammock
