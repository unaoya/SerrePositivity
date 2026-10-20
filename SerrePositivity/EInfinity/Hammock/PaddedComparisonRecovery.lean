module

public import SerrePositivity.EInfinity.Hammock.PaddedForwardColimit
public import SerrePositivity.EInfinity.Hammock.PaddingColimitRetraction

/-!
# 元の三列の比較から全語の標準射の回収

概要：padding 図式への元の三列の射は、元の全語の標準射を厳密に回収する。
方針：余極限比較の逆射の式と、元の padding 余錐の標準射への一致を使う。
規約：三列の語の等式による移送を含め、同じ元の射の等式を証明する。
使われ方：分数計算で得る比較の弱同値を元の hammock の標準射へ移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (H : Word ⥤ C)
  [HasColimit (Word.paddingFunctor ⋙ H)]

def paddedThreeComparison : H.obj Word.threeArrow ⟶ colimit (Word.paddingFunctor ⋙ H) :=
  H.map (eqToHom Word.padding_single_forward.symm) ≫
    colimit.ι (Word.paddingFunctor ⋙ H) (Word.single .forward)

lemma paddedThreeComparison_fac [HasColimit (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ H)] :
    (paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H)) =
      paddedThreeComparison H := paddedForwardColimitIso_inv_comparison H

lemma paddedThreeComparison_retraction [HasColimit H] :
    paddedThreeComparison H ≫ paddingColimitRetraction H = colimit.ι H Word.threeArrow := by
  change (H.map (eqToHom Word.padding_single_forward.symm) ≫
    colimit.ι (Word.paddingFunctor ⋙ H) (Word.single .forward)) ≫
      paddingColimitRetraction H = _
  rw [Category.assoc, paddingColimitRetraction_fac]
  exact colimit.w H (eqToHom Word.padding_single_forward.symm)

lemma paddedForwardColimit_comparison_recovery [HasColimit H]
    [HasColimit (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ H)] :
    (paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H)) ≫
          paddingColimitRetraction H = colimit.ι H Word.threeArrow := by
  rw [← Category.assoc, paddedThreeComparison_fac, paddedThreeComparison_retraction]

end SerrePositivity.EInfinity.Hammock
