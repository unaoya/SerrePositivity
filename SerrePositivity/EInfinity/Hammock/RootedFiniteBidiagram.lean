module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteDiagram
public import SerrePositivity.EInfinity.Hammock.RootedFiniteWordAction

/-!
# 元の有限部分集合と全語の二変数の graph 図式

概要：元の二方向の作用を strict な単体集合値図式へ束ねる。
方針：同じ元の nerve と全語の作用の可換性を使う。
規約：どちらの方向でも元の標準射を保持する。
使われ方：二つの元の余極限の交換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def graphWordDiagram : Word ⥤ Finset Q ⥤ SSet.{max u v} where
  obj a := graphDiagram T X Y a
  map f :=
    { app S := nerveMap (wordActionFunctor T X Y S f)
      naturality S R h := by
        change nerveMap (mapFunctor T X Y _ (leOfHom h) ⋙ wordActionFunctor T X Y R f) =
          nerveMap (wordActionFunctor T X Y S f ⋙ mapFunctor T X Y _ (leOfHom h))
        exact congrArg nerveMap (mapFunctor_wordAction T X Y (leOfHom h) f) }
  map_id a := by
    apply NatTrans.ext
    funext S
    change nerveMap (wordActionFunctor T X Y S (𝟙 a)) = 𝟙 _
    rw [wordActionFunctor_id]
    exact nerveFunctor.map_id (termCategory T X Y a S)
  map_comp f g := by
    apply NatTrans.ext
    funext S
    change nerveMap (wordActionFunctor T X Y S (f ≫ g)) =
      nerveMap (wordActionFunctor T X Y S f) ≫ nerveMap (wordActionFunctor T X Y S g)
    rw [wordActionFunctor_comp]
    exact nerveFunctor.map_comp (wordActionFunctor T X Y S f).toCatHom
      (wordActionFunctor T X Y S g).toCatHom

def graphWordProjection : graphWordDiagram T X Y ⟶
    Hammock.graphDiagram (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y) ⋙
      Functor.const (Finset Q) where
  app a := (graphCocone T X Y a).ι
  naturality a b f := by
    apply NatTrans.ext
    funext S
    change nerveMap (wordActionFunctor T X Y S f ⋙ projectionFunctor T X Y b S) =
      nerveMap (projectionFunctor T X Y a S ⋙ WordAction.functor f)
    exact congrArg nerveMap (projectionFunctor_wordAction T X Y S f).symm

end SerrePositivity.EInfinity.Hammock.RootedFinite
