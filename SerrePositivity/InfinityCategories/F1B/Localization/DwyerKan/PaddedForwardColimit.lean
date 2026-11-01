module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardColimit
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPaddedCollapse

/-!
# padding した forward 部分語の余極限と元の三列

概要：元の三列の値を余極限として回収し、元の包含による比較の後の像を照合する。
方針：一列への普遍性と元の三列の語の等式を合成し、逆射は標準包含で検査する。
規約：元の自然変換の colimMap への一致を証明する。
使われ方：分数計算の比較を元の三本矢の標準射へ移す工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (H : Word ⥤ C)
  [HasColimit (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ H)]

def paddedForwardColimitIso :
    colimit (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ H) ≅ H.obj Word.threeArrow :=
  forwardColimitIso (Word.paddingFunctor ⋙ H) ≪≫ H.mapIso (eqToIso Word.padding_single_forward)

lemma paddedForwardColimitIso_fac (a : Word) :
    colimit.ι (Word.forwardFunctor ⋙ Word.paddingFunctor ⋙ H) a ≫
        (paddedForwardColimitIso H).hom = H.map (Word.paddedCollapse a) := by
  change colimit.ι (Word.forwardFunctor ⋙ (Word.paddingFunctor ⋙ H)) a ≫
    ((forwardColimitIso (Word.paddingFunctor ⋙ H)).hom ≫
      (H.mapIso (eqToIso Word.padding_single_forward)).hom) = _
  rw [← Category.assoc, forwardColimitIso_fac]
  change H.map (Word.paddingFunctor.map (Word.forwardCollapse a)) ≫
    H.map (eqToHom Word.padding_single_forward) = H.map (Word.paddedCollapse a)
  exact (CategoryTheory.Functor.map_comp H _ _).symm

lemma paddedForwardColimitIso_inv_comparison [HasColimit (Word.paddingFunctor ⋙ H)] :
    (paddedForwardColimitIso H).inv ≫ colimMap
        (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H)) =
      H.map (eqToHom Word.padding_single_forward.symm) ≫
        colimit.ι (Word.paddingFunctor ⋙ H) (Word.single .forward) := by
  have hi : (forwardColimitIso (Word.paddingFunctor ⋙ H)).inv ≫ colimMap
      (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H)) =
        colimit.ι (Word.paddingFunctor ⋙ H) (Word.single .forward) := by
    apply (cancel_epi ((Word.paddingFunctor ⋙ H).mapIso forwardSingleIso).hom).1
    rw [← Category.assoc, forwardColimitIso_inv_fac, ι_colimMap]
    rfl
  change ((H.mapIso (eqToIso Word.padding_single_forward)).inv ≫
    (forwardColimitIso (Word.paddingFunctor ⋙ H)).inv) ≫ colimMap
      (Functor.whiskerRight Word.forwardInclusionNat (Word.paddingFunctor ⋙ H)) = _
  rw [Category.assoc, hi]
  rfl

end SerrePositivity.EInfinity.Hammock
