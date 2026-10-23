module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceSmallness
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.Core.PullbackSimplex

/-!
概要：各次数で小さい底上の coherent な図式の unstraightening の小ささ。
方針：引き戻しの単体を底の単体と射影の逆像の組へ単射で符号化する。
規約：図式の strict 性を仮定しない。全空間の定義は元の引き戻しを保つ。
使われ方：Kerodon Corollary 5.6.0.6、一般の coherent な図式の小さい left fibration の構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：引き戻しの単体は、小さい底と小さい逆像からなるとき小さい。
方針：底の単体で添字付けた逆像の直和へ単射で入れ、両射影による外延性を使う。
規約：二つの射の充填性は不要。
使われ方：Kerodon §5.5.2、普遍的な pointed-space 射影の小ささの底変換。 -/
lemma pullback_simplex_small_of_fibers {X Y B : SSet.{v}}
    (p : X ⟶ B) (q : Y ⟶ B) (n : ℕ) [Small.{u} (Y _⦋n⦌)]
    (hf : ∀ y : Y _⦋n⦌,
      Small.{u} {x : X _⦋n⦌ // p.app _ x = q.app _ y}) :
    Small.{u} ((pullback p q) _⦋n⦌) := by
  have (y : Y _⦋n⦌) : Small.{u} {x : X _⦋n⦌ // p.app _ x = q.app _ y} := hf y
  let T := Σ y : Y _⦋n⦌, {x : X _⦋n⦌ // p.app _ x = q.app _ y}
  let code : (pullback p q) _⦋n⦌ → T := fun x ↦
    ⟨(pullback.snd p q).app _ x, (pullback.fst p q).app _ x, pullbackSimplex_compat p q x⟩
  apply small_of_injective (f := code)
  intro x y h
  apply pullbackSimplex_ext p q
  · exact congrArg (fun t : T ↦ t.2.val) h
  · exact congrArg Sigma.fst h

/-- 概要：coherent な図式の unstraightening は、底が各次数で小さければ全空間も各次数で小さい。
方針：普遍的な pointed-space 射影の各単体上の小ささを引き戻す。
規約：図式 F は任意であり、通常の圏の nerve や strict な図式に制限しない。
使われ方：Kerodon Corollary 5.6.0.6、全空間を宇宙 u の単体集合へ縮小するための入力。 -/
instance leftUnstraightening_obj_small {B : SSet.{u + 1}}
    [∀ n, Small.{u} (B.obj n)] (F : B ⟶ SpaceInfinity.{u}) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((leftUnstraightening F).obj n) := by
  rcases n with ⟨⟨n⟩⟩
  exact pullback_simplex_small_of_fibers pointedSpaceProjection F n
    (fun y ↦ pointedSpaceProjection_simplexFiber_small _ (F.app _ y))

end SerrePositivity.InfinityCategories
