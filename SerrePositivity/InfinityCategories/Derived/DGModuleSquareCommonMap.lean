module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMapSimplex
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquareFunctor
/-!
概要：独立の係数圏宇宙を持つ dg 加群四角形の実関手像を共通宇宙で同定する。
方針：既存の混在宇宙の二つの合成三角形の比較を、正方形の二セルで貼る。
規約：四辺・対角・両次数 −1 成分を変えない。
使われ方：全加群間の dg 関手の混在宇宙での cone 保存。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] [Small.{u} D]
  {C : Type w} [DGCategory R C] [Small.{u} C]
  {W X Y Z : ModuleCategory R D} (s : DGModuleSquareData R D W X Y Z)

lemma map_square_common (F : DGFunctor R (RightModule R D) (RightModule R C)) :
    uliftSquare.{max (u + 1) v, max (u + 1) v w t} s.square ≫
        dgNerveCommonMap.{u, max (u + 1) v, max (u + 1) w, t} F =
      uliftSquare.{max (u + 1) w, max (u + 1) v w t} (s.map F).square := by
  apply square_isPushout.hom_ext
  · rw [← Category.assoc, uliftSquare_triangle, square_upper,
      uliftSquare_triangle, square_upper, dgNerveCommonMap_simplex, map_upperTriangle]
  · rw [← Category.assoc, uliftSquare_triangle, square_lower,
      uliftSquare_triangle, square_lower, dgNerveCommonMap_simplex, map_lowerTriangle]

end SerrePositivity.InfinityCategories.DGModuleSquareData
