module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CostructuredArrowDiagram
public import Mathlib.CategoryTheory.Grothendieck

/-!
# 全図式の射影の comma 圏から元の fiber への移送

概要：Grothendieck 射影への脚に沿って元の fiber の対象と射を移送する。
方針：元の Cat 値関手の恒等・合成則で型を揃え、元の fiber 射を移送する。
規約：まず同じ宇宙の小圏で構成する。単体集合モデルは要求しない。
使われ方：Thomason 比較の comma 図式から元の図式への自然変換。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

variable {D : Type u} [Category.{u} D] (G : D ⥤ Cat.{u, u})

/-- 元の全図式の射影を用いた comma 図式。 -/
abbrev commaDiagram : D ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram (Grothendieck.forget G)

/-- 同じ射影への脚に沿って元の fiber の対象と射を移送する。 -/
def transport (d : D) : CostructuredArrow (Grothendieck.forget G) d ⥤ G.obj d where
  obj S := (G.map S.hom).toFunctor.obj S.left.fiber
  map {S T} f := eqToHom (by
      rw [← CostructuredArrow.w f, G.map_comp]
      rfl) ≫ (G.map T.hom).toFunctor.map f.left.fiber
  map_id S := by
    dsimp only [CostructuredArrow.id_left]
    rw [Grothendieck.id_fiber, eqToHom_map, eqToHom_trans]
    rfl
  map_comp {S T U} f g := by
    have hh : (G.map T.hom).toFunctor =
        (G.map g.left.base).toFunctor ⋙ (G.map U.hom).toFunctor := by
      rw [← CostructuredArrow.w g, G.map_comp]
      rfl
    simp only [CostructuredArrow.comp_left, Grothendieck.comp_fiber,
      CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc]
    rw [CategoryTheory.Functor.congr_hom hh f.left.fiber]
    simp only [Functor.comp_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

/-- 終域の元の射による後合成と移送は、関手の等式として可換。 -/
lemma transport_naturality {d e : D} (f : d ⟶ e) :
    CostructuredArrow.map (S := Grothendieck.forget G) f ⋙ transport G e =
      transport G d ⋙ (G.map f).toFunctor := by
  refine CategoryTheory.Functor.ext (fun S => ?_) ?_
  · change (G.map (S.hom ≫ f)).toFunctor.obj S.left.fiber =
      (G.map f).toFunctor.obj ((G.map S.hom).toFunctor.obj S.left.fiber)
    rw [G.map_comp]
    rfl
  · intro S T h
    dsimp only [Functor.comp_map, transport]
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map, Category.assoc]
    change eqToHom _ ≫ (G.map (T.hom ≫ f)).toFunctor.map h.left.fiber = _
    rw [CategoryTheory.Functor.congr_hom congr($(G.map_comp T.hom f).toFunctor)]
    simp only [eqToHom_trans_assoc]
    rfl

/-- 各脚に沿う元の移送を、厳密な Cat 値の自然変換へ束ねる。 -/
def transportComparison : commaDiagram G ⟶ G where
  app d := (transport G d).toCatHom
  naturality _ _ f := Cat.Hom.ext (transport_naturality G f)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
