module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：形状同型による前合成を打ち消し、元の全比較の類を端点込みで保持する。
方針：逆形状へ制限した同型の両端を逆同型則で輸送し、等号による端点輸送を相殺する。
規約：比較を選び直さない。使われ方：極限錐の相対同型を元の fiber 正方形へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B X : SSet.{u}} (e : A ≅ B) {F G : B ⟶ X}
  (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ F) (e.hom ≫ G))

def cancelPrecompIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  eqToIso (congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k))
    (e.inv_hom_id_assoc F).symm) ≪≫ α.precomp e.inv ≪≫
  eqToIso (congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) (e.inv_hom_id_assoc G))

lemma cancelPrecompIso_arrow : Arrow.mk (cancelPrecompIso e α).hom =
    Arrow.mk (homPre e.inv α.hom) := by
  unfold cancelPrecompIso
  simp only [Iso.trans_hom, eqToIso.hom]
  let f := homPre e.inv α.hom
  let h₀ := congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) (e.inv_hom_id_assoc F).symm
  let h₁ := congrArg (fun k ↦ HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex k)) (e.inv_hom_id_assoc G)
  change Arrow.mk (eqToHom h₀ ≫ f ≫ eqToHom h₁) = Arrow.mk f
  exact (arrow_mk_eqToHom_comp h₀ (f ≫ eqToHom h₁)).trans (arrow_mk_comp_eqToHom f h₁)

end SerrePositivity.KST.LocalizingInvariants
