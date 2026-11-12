module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：自然同型で可換な正方形による指定 Hom 写像の全単射の移送。
方針：左右の充満忠実な関手と端点の同型による Hom の全単射を消去する。
規約：正方形の横方向に大域的な充満忠実性を要求しない。
使われ方：内部 Hom の交換による Kan 制限の全パラメータ判定。
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：縦の関手が充満忠実な正方形は、下の指定 Hom の全単射を上へ移す。
方針：自然性で合成の Hom 写像を同定し、縦の単射性で合成から上の全単射を得る。
規約：対象 x・y の Hom だけに下の全単射を要求する。
使われ方：定値族の転置前後で実際の制限の Hom 写像を比較する。 -/
lemma homMap_bijective_of_iso_square
    {C C' D D' : Type u} [Category.{u} C] [Category.{u} C']
    [Category.{u} D] [Category.{u} D']
    (P : C ⥤ D) (Q : C' ⥤ D') (L : C ⥤ C') (M : D ⥤ D')
    (hL : L.FullyFaithful) (hM : M.FullyFaithful) (e : P ⋙ M ≅ L ⋙ Q)
    (x y : C) (hQ : Function.Bijective (Q.map : (L.obj x ⟶ L.obj y) → _)) :
    Function.Bijective (P.map : (x ⟶ y) → _) := by
  let E := (e.app x).homCongr (e.app y)
  have he : (fun α : x ⟶ y ↦ E (M.map (P.map α))) =
      (fun α : x ⟶ y ↦ Q.map (L.map α)) := by
    funext α
    change e.inv.app x ≫ ((P ⋙ M).map α ≫ e.hom.app y) = (L ⋙ Q).map α
    rw [← Category.assoc, ← e.inv.naturality α, Category.assoc,
      e.inv_hom_id_app, Category.comp_id]
  have hb : Function.Bijective (fun α : x ⟶ y ↦ E (M.map (P.map α))) := by
    rw [he]
    exact hQ.comp (hL.map_bijective x y)
  have hb' : Function.Bijective ((fun β : P.obj x ⟶ P.obj y ↦ E (M.map β)) ∘
      (P.map : (x ⟶ y) → _)) := hb
  exact hb'.of_comp_left (E.injective.comp (hM.map_bijective _ _).1)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
