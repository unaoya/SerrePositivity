module

public import SerrePositivity.EInfinity.Hammock.FixedObjectWordDiagram

/-!
# 固定対象の図式の元の係数自然変換

概要：元の相対圏の全図式の比較と対象表示から全 zigzag の自然変換を作る。
方針：元の固定端点の関手の合成と全語の作用の可換式を使う。
規約：元の全対象・全縦射と端点表示を保持する。
使われ方：自由 hammock の左右比較射の全係数自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uI vI uO uP
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory SimplicialLocalization
variable {I : Type uI} [Category.{vI} I] (D E : I ⥤ RelativeCategory.{u})
  {O : Type uO} {P : Type uP}
  (p : (i : I) → O → (D.obj i).category) (q : (i : I) → P → (E.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).functor.obj (p i X) = p j X)
  (hq : ∀ {i j : I} (θ : i ⟶ j) (X : P), (E.map θ).functor.obj (q i X) = q j X)
  (A : D ⟶ E) (s : O → P) (hA : ∀ i X, (A.app i).functor.obj (p i X) = q i (s X))
def categoryMap (w : Word) (X Y : O) :
    zigzagDiagram D p hp w X Y ⟶ zigzagDiagram E q hq w (s X) (s Y) where
  app i := (Zigzag.Relative.fixedFunctor (A.app i) (hA i X) (hA i Y)).toCatHom
  naturality i j θ := by
    apply Cat.Hom.ext
    have he := congrArg (fun K : D.obj i ⟶ E.obj j => K.functor) (A.naturality θ)
    change (D.map θ).functor ⋙ (A.app j).functor =
      (A.app i).functor ⋙ (E.map θ).functor at he
    change Zigzag.Relative.fixedFunctor (D.map θ) (hp θ X) (hp θ Y) ⋙
        Zigzag.Relative.fixedFunctor (A.app j) (hA j X) (hA j Y) =
      Zigzag.Relative.fixedFunctor (A.app i) (hA i X) (hA i Y) ⋙
        Zigzag.Relative.fixedFunctor (E.map θ) (hq θ (s X)) (hq θ (s Y))
    exact (Zigzag.Relative.fixedFunctor_comp (D.map θ) (A.app j)
      (hp θ X) (hp θ Y) (hA j X) (hA j Y)).symm.trans
        ((Zigzag.Relative.fixedFunctor_congr (w := w)
          (F := (D.map θ).comp (A.app j)) (G := (A.app i).comp (E.map θ)) he
          ((congrArg (A.app j).functor.obj (hp θ X)).trans (hA j X))
          ((congrArg (A.app j).functor.obj (hp θ Y)).trans (hA j Y))
          ((congrArg (E.map θ).functor.obj (hA i X)).trans (hq θ (s X)))
          ((congrArg (E.map θ).functor.obj (hA i Y)).trans (hq θ (s Y)))).trans
            (Zigzag.Relative.fixedFunctor_comp (A.app i) (E.map θ)
              (hA i X) (hA i Y) (hq θ (s X)) (hq θ (s Y))))
def graphMap (w : Word) (X Y : O) :
    graphDiagram D p hp w X Y ⟶ graphDiagram E q hq w (s X) (s Y) :=
  Functor.whiskerRight (categoryMap D E p q hp hq A s hA w X Y) nerveFunctor

def categoryWordMap (X Y : O) : categoryWordDiagram D p hp X Y ⟶
    categoryWordDiagram E q hq (s X) (s Y) where
  app w := categoryMap D E p q hp hq A s hA w X Y
  naturality a b f := by
    apply NatTrans.ext
    funext i
    apply Cat.Hom.ext
    exact (Zigzag.Relative.wordAction_fixedFunctor_eq (A.app i) (hA i X) (hA i Y) f).symm
def graphWordMap (X Y : O) : graphWordDiagram D p hp X Y ⟶
    graphWordDiagram E q hq (s X) (s Y) :=
  Functor.whiskerRight (categoryWordMap D E p q hp hq A s hA X Y)
    ((Functor.whiskeringRight (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor)
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
