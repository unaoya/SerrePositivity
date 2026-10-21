module

public import SerrePositivity.EInfinity.Hammock.ForwardZigzagDiscrete
public import SerrePositivity.EInfinity.Hammock.BackwardZigzagDiscrete
public import SerrePositivity.EInfinity.Hammock.RelativeFixedZigzagFunctor

/-!
# 元の単一列の評価の相対自然性

概要：元の一列の値を同じ端点の Hom へ回収する。
方針：全縦射と端点移送を保持する。
規約：モデル構造を要求しない。
使われ方：全自由作用素の Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {X Y : C} {X' Y' : D} (F : LocalizerMorphism W V)
  (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')

lemma ForwardZigzag.value_relative (S : Zigzag W (Word.single .forward) X Y) :
    value ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
      eqToHom hX.symm ≫ F.functor.map (value S) ≫ eqToHom hY := by
  dsimp only [value, Zigzag.Relative.fixedFunctor, Functor.comp_obj,
    Zigzag.Relative.functor, Zigzag.Relative.obj, Zigzag.EndpointChange.functor,
    Zigzag.EndpointChange.obj]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]

lemma BackwardZigzag.value_relative (S : Zigzag W (Word.single .backward) X Y) :
    (value ((Zigzag.Relative.fixedFunctor F hX hY).obj S)).val =
      eqToHom hY.symm ≫ F.functor.map (value S).val ≫ eqToHom hX := by
  dsimp only [value, Zigzag.Relative.fixedFunctor, Functor.comp_obj,
    Zigzag.Relative.functor, Zigzag.Relative.obj, Zigzag.EndpointChange.functor,
    Zigzag.EndpointChange.obj]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
end SerrePositivity.EInfinity.Hammock
