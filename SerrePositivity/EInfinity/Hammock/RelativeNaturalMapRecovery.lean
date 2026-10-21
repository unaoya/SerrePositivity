module

public import SerrePositivity.EInfinity.Hammock.RelativeNaturalGraphHomotopy
public import SerrePositivity.EInfinity.Hammock.RelativeNaturalWordRows
public import SerrePositivity.EInfinity.Hammock.RelativeCompositionPoints
public import SerrePositivity.EInfinity.Hammock.PointActions
public import SerrePositivity.EInfinity.Hammock.ColimitArrowMap

/-!
# 比較ホモトピーの両端と元の前後合成の一致

概要：二つの行の像を元の相対写像と η の前後合成へ厳密に回収する。
方針：元の標準射で合成を計算し、外側の恒等列を単位則で消す。
規約：既存の colimitMap・arrowMap・合成を使う。
使われ方：全語のホモトピーの両端の同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor) (w : Word) (X Y : C)

lemma beforeMap_recovery : beforeMap η w X Y = graphInclusion W X Y w ≫
    Relative.colimitMap F X Y ≫ postcomposePointMap (F.functor.obj X) (arrowMap V (η.app Y)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj w)).app n
    (σ ⋙ beforeFunctor η w X Y) = composePoint V _ _ _
      ((Relative.colimitMap F X Y).app n ((graphInclusion W X Y w).app n σ))
      (arrowPoint V (η.app Y) n)
  rw [Relative.graphInclusion_point]
  have h : (graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj w)).app n
      (σ ⋙ beforeFunctor η w X Y) =
      composePoint V _ _ _ (arrowPoint V (𝟙 (F.functor.obj X)) n)
        (composePoint V _ _ _
          ((graphInclusion V (F.functor.obj X) (F.functor.obj Y) w).app n
            (σ ⋙ Zigzag.Relative.functor F)) (arrowPoint V (η.app Y) n)) := by
    rw [arrowPoint, arrowPoint, composePoint_inclusions, composePoint_inclusions]
    rfl
  rw [composePoint_identity_left] at h
  exact h

lemma afterMap_recovery : afterMap η w X Y = graphInclusion W X Y w ≫
    Relative.colimitMap G X Y ≫ precomposePointMap (arrowMap V (η.app X)) (G.functor.obj Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  change (graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj w)).app n
    (σ ⋙ afterFunctor η w X Y) = composePoint V _ _ _ (arrowPoint V (η.app X) n)
      ((Relative.colimitMap G X Y).app n ((graphInclusion W X Y w).app n σ))
  rw [Relative.graphInclusion_point]
  have h : (graphInclusion V (F.functor.obj X) (G.functor.obj Y) (wordFunctor.obj w)).app n
      (σ ⋙ afterFunctor η w X Y) = composePoint V _ _ _ (arrowPoint V (η.app X) n)
        (composePoint V _ _ _
          ((graphInclusion V (G.functor.obj X) (G.functor.obj Y) w).app n
            (σ ⋙ Zigzag.Relative.functor G)) (arrowPoint V (𝟙 (G.functor.obj Y)) n)) := by
    rw [arrowPoint, arrowPoint, composePoint_inclusions, composePoint_inclusions]
    rfl
  rw [composePoint_identity_right] at h
  exact h

end SerrePositivity.EInfinity.Hammock.RelativeNatural
