module
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
/-!
概要：両端の閉同型を持つ可換四角形から、実 cone の同型を得る。
方針：arrow 圏の同型を標準 cone 関手へ送る。
規約：元の四角形の射と両端同型を保持する。
使われ方：巨大な延長値の型展開を避ける、表示 cone の評価比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeIsoOfSquare {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (a : M ≅ M') (b : N ≅ N')
    (h : a.hom ≫ g = f ≫ b.hom) :=
  (moduleConeFunctor A D).mapIso (Arrow.isoMk' f g a b h)

end SerrePositivity.DifferentialGraded
