module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.RightMixedFamily

/-!
概要：元の通常の射と両 frame の全自然比較との単位三角形。
方針：同じ source augmentation の前合成と right augmentation の後合成を照合する。
規約：零単体だけでなく全次数・全標的で同じ射を保持する。
使われ方：coherent な局所化比較の零単体正規化の実入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の全射を同じ source augmentation に前合成して全 Hom 族へ送る。
方針：元の cosimplicial Hom の自然変換を使う。
規約：全次数・全標的に一つの自然変換。
使われ方：元の射と同じ roof の照合。 -/
def sourceFrameOrdinaryHomUnit : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ordinaryHomFamily X ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj :=
  { app := fun Y =>
      { app := fun n => ↾fun f => q.augmentation.app n.unop ≫ f
        naturality := by
          intro n m a
          ext f
          change X ⟶ Y at f
          change q.augmentation.app m.unop ≫ (f ≫ 𝟙 Y) =
            q.obj.map a.unop ≫ (q.augmentation.app n.unop ≫ f)
          have h : q.obj.map a.unop ≫ q.augmentation.app n.unop =
              q.augmentation.app m.unop := by
            exact (q.augmentation.naturality a.unop).trans (Category.comp_id _)
          exact (congrArg (q.augmentation.app m.unop ≫ ·) (Category.comp_id f)).trans
            ((congrArg (fun (t : q.obj.obj m.unop ⟶ X) => t ≫ f) h.symm).trans
              (Category.assoc _ _ _)) }
    naturality := by
      intro Y Z f
      ext n g
      change X ⟶ Y at g
      change q.augmentation.app n.unop ≫ (g ≫ f) =
        (q.augmentation.app n.unop ≫ g) ≫ f
      exact (Category.assoc _ _ _).symm }

/-- 概要：元の全射は同じ source augmentation 合成へ送られる。
方針：同じ自然変換の成分を読む。
規約：零単体を含む全次数。使われ方：元の局所化射の正規化。 -/
lemma sourceFrameOrdinaryHomUnit_app (Y : C) (n : SimplexCategoryᵒᵖ) (f : X ⟶ Y) :
    (((sourceFrameOrdinaryHomUnit q).app Y).app n) f = q.augmentation.app n.unop ≫ f := rfl

/-- 概要：元の射の両 frame への比較は混合 Hom の全族で同じ三角形を作る。
方針：元の augmentation の前後合成の結合律を全成分に使う。
規約：全標的と全次数の厳密な自然変換の等式。
使われ方：coherent な比較の単位と元の零単体の同定。 -/
lemma rightMixed_unit_triangle :
    sourceFrameOrdinaryHomUnit q ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft q r =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomUnit r X ≫ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight q r := by
  ext Y n f
  change (q.augmentation.app n.unop ≫ f) ≫ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app n =
    q.augmentation.app n.unop ≫ (f ≫ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app n)
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
