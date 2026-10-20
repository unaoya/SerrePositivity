module

public import SerrePositivity.EInfinity.Hammock.WordForwardFixed
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# forward 部分語で前合成した元の図式の余極限

概要：元の forward 部分語図式の余極限は一列 forward の値である。
方針：元の部分語包含と一列への合成の二つの余錐の式を、包含の同型性で消去する。
規約：固定語の合成写像の弱同値性は仮定しない。任意の値の圏での普遍性を証明する。
使われ方：両端 padding 後の元の三列の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

def forwardSingleIso : Word.forwardCore (Word.single .forward) ≅ Word.single .forward := by
  have := Word.forwardInclusion_isIso (Word.single .forward) (fun _ => rfl)
  exact asIso (Word.forwardInclusion (Word.single .forward))

lemma forwardCollapse_fac (a : Word) :
    Word.forwardInclusion (Word.forwardCore a) ≫ Word.forwardCollapse a =
      Word.forwardMap (Word.forwardCollapse a) ≫ forwardSingleIso.hom :=
  (Word.forwardMap_fac (Word.forwardCollapse a)).symm

variable {C : Type u} [Category.{v} C] (H : Word ⥤ C)

def forwardColimitCocone : Cocone (Word.forwardFunctor ⋙ H) where
  pt := H.obj (Word.single .forward)
  ι :=
    { app a := H.map (Word.forwardCollapse a)
      naturality a b f := by
        change H.map (Word.forwardMap f) ≫ H.map (Word.forwardCollapse b) =
          H.map (Word.forwardCollapse a) ≫ 𝟙 _
        rw [Category.comp_id, ← CategoryTheory.Functor.map_comp,
          Word.forwardCollapse_naturality] }

def forwardColimitDesc (s : Cocone (Word.forwardFunctor ⋙ H)) :
    H.obj (Word.single .forward) ⟶ s.pt :=
  (H.mapIso forwardSingleIso).inv ≫ s.ι.app (Word.single .forward)

lemma forwardColimitDesc_fac (s : Cocone (Word.forwardFunctor ⋙ H)) (a : Word) :
    H.map (Word.forwardCollapse a) ≫ forwardColimitDesc H s = s.ι.app a := by
  have := Word.forwardInclusion_isIso (Word.forwardCore a) (Word.forwardCore_direction a)
  apply (cancel_epi (H.map (Word.forwardInclusion (Word.forwardCore a)))).1
  calc
    _ = H.map (Word.forwardMap (Word.forwardCollapse a)) ≫
        s.ι.app (Word.single .forward) := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, forwardCollapse_fac,
        CategoryTheory.Functor.map_comp]
      change (H.map (Word.forwardMap (Word.forwardCollapse a)) ≫
        (H.mapIso forwardSingleIso).hom) ≫
          ((H.mapIso forwardSingleIso).inv ≫ s.ι.app (Word.single .forward)) = _
      rw [Category.assoc, Iso.hom_inv_id_assoc]
    _ = s.ι.app (Word.forwardCore a) := s.w (Word.forwardCollapse a)
    _ = _ := by
      have he := s.w (Word.forwardInclusion a)
      change H.map (Word.forwardMap (Word.forwardInclusion a)) ≫ s.ι.app a = _ at he
      rw [Word.forwardMap_forwardInclusion] at he
      exact he.symm

def forwardColimitCocone_isColimit : IsColimit (forwardColimitCocone H) where
  desc := forwardColimitDesc H
  fac := forwardColimitDesc_fac H
  uniq s m hm := by
    change H.obj (Word.single .forward) ⟶ s.pt at m
    apply (cancel_epi (H.mapIso forwardSingleIso).hom).1
    change (H.mapIso forwardSingleIso).hom ≫ m = (H.mapIso forwardSingleIso).hom ≫
      ((H.mapIso forwardSingleIso).inv ≫ s.ι.app (Word.single .forward))
    rw [Iso.hom_inv_id_assoc]
    have he := hm (Word.single .forward)
    change H.map (Word.forwardCollapse (Word.single .forward)) ≫ m = _ at he
    rw [Word.toSingleForward_unique (Word.forwardCollapse (Word.single .forward))
      forwardSingleIso.hom] at he
    exact he

def forwardColimitIso [HasColimit (Word.forwardFunctor ⋙ H)] :
    colimit (Word.forwardFunctor ⋙ H) ≅ H.obj (Word.single .forward) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (forwardColimitCocone_isColimit H)

lemma forwardColimitIso_fac [HasColimit (Word.forwardFunctor ⋙ H)] (a : Word) :
    colimit.ι (Word.forwardFunctor ⋙ H) a ≫ (forwardColimitIso H).hom =
      H.map (Word.forwardCollapse a) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ _

lemma forwardColimitIso_inv_fac [HasColimit (Word.forwardFunctor ⋙ H)] :
    (H.mapIso forwardSingleIso).hom ≫ (forwardColimitIso H).inv =
      colimit.ι (Word.forwardFunctor ⋙ H) (Word.single .forward) := by
  apply (cancel_mono (forwardColimitIso H).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, forwardColimitIso_fac]
  exact congrArg H.map (Word.toSingleForward_unique forwardSingleIso.hom
    (Word.forwardCollapse (Word.single .forward)))

end SerrePositivity.EInfinity.Hammock
