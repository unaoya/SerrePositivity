module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceFrame

/-!
# Cofibrant frame の Hom と元の sourceFrameHom の厳密な同型

概要：全部分圏の Hom の包みだけを外し、同じ元の代数射を回収する。
方針：全次数の hom と homMk を逆にし、元の作用素との可換性を確認する。
規約：frame・対象・射・全次数を変更せず、弱同値による置換もしない。
使われ方：元の全単体の比較を cofibrant source frame の全体へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

def cofibrantSourceFrameHomIso :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (cofibrantSourceFrame A X)).obj Y ≅
      ((sourceFrameHom A).obj (op X.obj)).obj Y.obj where
  hom :=
    { app _ := ↾fun f => f.hom
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun f => ObjectProperty.homMk f
      naturality _ _ _ := rfl }

lemma cofibrantSourceFrameHomIso_hom {n : ℕ}
    (f : ((cofibrantSourceFrame A X).obj ⦋n⦌) ⟶ Y) :
    (cofibrantSourceFrameHomIso A X Y).hom.app (op ⦋n⦌) f = f.hom := rfl

end SerrePositivity.EInfinity.BarrattEccles
