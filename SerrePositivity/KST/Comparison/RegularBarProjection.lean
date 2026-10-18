module

public import SerrePositivity.KST.Comparison.RegularBar
public import SerrePositivity.KST.Comparison.MonoidComponents

/-!
# 正則 bar の射影

概要：正則作用の全空間からモノイドの分類空間への射影を構成する。
方針：各射列のラベルを保って一対象圏へ送り、二重単体的 nerve の対角に制限する。
規約：Segal 1974 Proposition 1.5 の普遍 bar 束。fibration 性は別の主張である。
使われ方：群完備化比較でのホモトピーファイバーの同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：正則 bar の全空間から分類空間への標準射影。
方針：射列をラベルの射列へ送り、面と退化との自然性を直接確認する。
規約：Segal 1974 Proposition 1.5。全次数のモノイドが群である必要はない。
使われ方：普遍束の構造写像。
-/
def regularBarProjection (M : SimplicialObject MonCat.{u}) : regularBar M ⟶ monoidBar M where
  app n := TypeCat.ofHom (fun F => F ⋙ regularActionProjection (M.obj n))
  naturality _ _ _ := rfl

/--
概要：各モノイドの元を正則 bar のファイバーへ送る標準写像。
方針：与えられた元の正則作用の対象で定数の射列を作る。
規約：Segal 1974 Proposition 1.5 のファイバー比較の入口。
使われ方：M と普遍 bar 束のホモトピーファイバーの比較。
-/
def regularBarFiberMap (M : SimplicialObject MonCat.{u}) : monoidSpace M ⟶ regularBar M where
  app n := TypeCat.ofHom (fun (m : M.obj n) =>
    (Functor.const (Fin (n.unop.len + 1))).obj (RegularAction.mk m))
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro m
    change M.obj i at m
    change (Functor.const (Fin (j.unop.len + 1))).obj (RegularAction.mk ((M.map f).hom m)) =
      (SimplexCategory.toCat.map f.unop).toFunctor ⋙
        (Functor.const (Fin (i.unop.len + 1))).obj (RegularAction.mk m) ⋙
          regularActionMap (M.map f).hom
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro a b h
    apply Subtype.ext
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (1 : M.obj j) = (M.map f).hom 1
    exact (map_one _).symm

/--
概要：標準ファイバー写像の分類空間への像は基点に定数である。
方針：定数の射列のラベルを準同型の単位保存と比較する。
規約：Segal 1974 Proposition 1.5。厳密ファイバーへの因子化だけを主張する。
使われ方：ホモトピーファイバー比較の三角形。
-/
theorem regularBarFiberMap_projection (M : SimplicialObject MonCat.{u}) :
    regularBarFiberMap M ≫ regularBarProjection M = SSet.const (monoidBarBasepoint M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro m
  change M.obj n at m
  change (Functor.const (Fin (n.unop.len + 1))).obj (RegularAction.mk m) ⋙
      regularActionProjection (M.obj n) =
    (SimplexCategory.toCat.map (SimplexCategory.const n.unop ⦋0⦌ 0)).toFunctor ⋙
      (Functor.const (Fin 1)).obj (SingleObj.star (M.obj (op ⦋0⦌))) ⋙
        SingleObj.mapHom _ _ (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (1 : M.obj n) = (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom 1
  exact (map_one _).symm

end SerrePositivity.KST.Comparison
