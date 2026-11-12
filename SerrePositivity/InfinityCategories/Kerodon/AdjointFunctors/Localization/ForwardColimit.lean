module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardFixed
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# forward 部分語で前合成した元の図式の余極限

概要：元の forward 部分語図式の余極限は一列 forward の値である。
方針：元の部分語包含と一列への合成の二つの余錐の式を、包含の同型性で消去する。
規約：固定語の合成写像の弱同値性は仮定しない。任意の値の圏での普遍性を証明する。
使われ方：両端 padding 後の元の三列の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

def forwardSingleIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardInclusion_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (fun _ => rfl)
  exact asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))

lemma forwardCollapse_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a) ≫ forwardSingleIso.hom :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap_fac (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)).symm

variable {C : Type u} [Category.{v} C] (H : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ C)

def forwardColimitCocone : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H) where
  pt := H.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
  ι :=
    { app a := H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)
      naturality a b f := by
        change H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f) ≫ H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse b) =
          H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a) ≫ 𝟙 _
        rw [Category.comp_id, ← CategoryTheory.Functor.map_comp,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse_naturality] }

def forwardColimitDesc (s : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H)) :
    H.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) ⟶ s.pt :=
  (H.mapIso forwardSingleIso).inv ≫ s.ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)

lemma forwardColimitDesc_fac (s : Cocone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H)) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a) ≫ forwardColimitDesc H s = s.ι.app a := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardInclusion_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore_direction a)
  apply (cancel_epi (H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a)))).1
  calc
    _ = H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)) ≫
        s.ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, forwardCollapse_fac,
        CategoryTheory.Functor.map_comp]
      change (H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)) ≫
        (H.mapIso forwardSingleIso).hom) ≫
          ((H.mapIso forwardSingleIso).inv ≫ s.ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = s.ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) := s.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a)
    _ = _ := by
      have he := s.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a)
      change H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusion a)) ≫ s.ι.app a = _ at he
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMap_forwardInclusion] at he
      exact he.symm

def forwardColimitCocone_isColimit : IsColimit (forwardColimitCocone H) where
  desc := forwardColimitDesc H
  fac := forwardColimitDesc_fac H
  uniq s m hm := by
    change H.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) ⟶ s.pt at m
    apply (cancel_epi (H.mapIso forwardSingleIso).hom).1
    change (H.mapIso forwardSingleIso).hom ≫ m = (H.mapIso forwardSingleIso).hom ≫
      ((H.mapIso forwardSingleIso).inv ≫ s.ι.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
    rw [Iso.hom_inv_id_assoc]
    have he := hm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
    change H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) ≫ m = _ at he
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toSingleForward_unique (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
      forwardSingleIso.hom] at he
    exact he

def forwardColimitIso [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H)] :
    colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H) ≅ H.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (forwardColimitCocone_isColimit H)

lemma forwardColimitIso_fac [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H)] (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H) a ≫ (forwardColimitIso H).hom =
      H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ _

lemma forwardColimitIso_inv_fac [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H)] :
    (H.mapIso forwardSingleIso).hom ≫ (forwardColimitIso H).inv =
      colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ H) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) := by
  apply (cancel_mono (forwardColimitIso H).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, forwardColimitIso_fac]
  exact congrArg H.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toSingleForward_unique forwardSingleIso.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
