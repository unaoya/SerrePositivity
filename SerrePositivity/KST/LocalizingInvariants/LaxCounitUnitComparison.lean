module

public import SerrePositivity.KST.LocalizingInvariants.LaxCounitRightHom
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomExchange
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyIsoPostcomp

/-!
概要：元の cofiber の指定右辺を C 随伴の単位へ送る関手同型。
方針：指定右辺の第一射影の逆を使い、単位の自然性と相殺する。
規約：関手同型の存在だけでなく元の自然変換の類を保持する。
使われ方：一般商の二脚と元の fiber 四角形の二次の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxCounit
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def rightCompatibleFromCIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cofiber p q)
    ((laxFst p q).hom ≫ LaxInclusion.fromC p q) :=
  cofiber_unitIso p q ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (rightFstIso p q).symm (LaxInclusion.fromC p q)

lemma rightHom_unit_naturality : rightHom p q ≫ (cofiber_unitIso p q).hom =
    (LaxInclusion.fromCAdjunction p q).unitHom ≫
      homPostFromIdentityComp (cofiber p q) (laxFst p q).hom
        (LaxInclusion.fromC p q) (rightHom p q) := by
  exact identityHom_exchange_comp (cofiber p q)
    (laxFst p q).hom (LaxInclusion.fromC p q) (rightHom p q)
    (LaxInclusion.fromCAdjunction p q).unitHom

lemma rightCompatibleFromCIso_right :
    rightHom p q ≫ (rightCompatibleFromCIso p q).hom =
      (LaxInclusion.fromCAdjunction p q).unitHom := by
  change rightHom p q ≫ ((cofiber_unitIso p q).hom ≫ _) = _
  rw [← Category.assoc, rightHom_unit_naturality, Category.assoc]
  have he : homPostFromIdentityComp (cofiber p q) (laxFst p q).hom
      (LaxInclusion.fromC p q) (rightHom p q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (rightFstIso p q).symm (LaxInclusion.fromC p q)).hom =
        𝟙 _ := by
    change homPost ((laxFst p q).hom ≫ LaxInclusion.fromC p q) (rightHom p q) ≫ _ = _
    rw [homPost_comp]
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorIso_postcomp_hom]
    change homPost (LaxInclusion.fromC p q) (rightFstIso p q).hom ≫
      homPost (LaxInclusion.fromC p q) (rightFstIso p q).inv = 𝟙 _
    rw [← homPost_homComp, Iso.hom_inv_id, homPost_id]
  rw [he, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.LaxCounit
