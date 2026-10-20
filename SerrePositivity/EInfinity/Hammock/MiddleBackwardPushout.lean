module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardPullback

/-!
# 中央の自明 cofibration を右ブロック全体の pushout で置換する

概要：元の X,Y を固定し、中央を指定中間対象の恒等列にした実際の zigzag を構成。
方針：右ブロックの包含と中央の正方形を貼り、元の全体からの縦弱同値を作る。
規約：同じ語・同じ左右の外側の射を使う。長さ零も含む。
使われ方：中央の恒等列の包含に向かう unit の成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def pushoutInput (L : ComposableArrows C n) (R : ComposableArrows C m)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) : InitialReplacement C m :=
  ⟨R, L.obj (Fin.last n), c⟩

def pushoutObj (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) (hc : trivialCofibrations C c)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    Zigzag (weakEquivalences C) (word n m) X Y :=
  ZigzagAppend.obj
    (ZigzagAppend.obj (leftBoundaryBlock L a ha)
      (BackwardZigzag.obj (𝟙 (L.obj (Fin.last n))) ((weakEquivalences C).id_mem _)))
    (pushoutRightBoundary (pushoutInput L R c) hc b hb)

def pushoutInclusion (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) (hc : trivialCofibrations C c)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    Zigzag.Hom (obj L R a ha c hc.2 b hb) (pushoutObj L R a ha c hc b hb) := by
  let f := Zigzag.MovingHom.id (leftBoundaryBlock L a ha)
  let g := BackwardZigzag.movingHom hc.2 ((weakEquivalences C).id_mem _)
    (𝟙 (L.obj (Fin.last n))) c ((weakEquivalences C).id_mem _) hc.2 rfl
  have hj : HEq (f.app (Fin.last (leftBoundaryWord n).length)) (g.app 0) :=
    Zigzag.MovingHom.id_last (leftBoundaryBlock L a ha)
  let fg := ZigzagAppend.Moving.map f g hj
  let k := pushoutRightBoundaryInclusion (pushoutInput L R c) hc b hb
  have hj' : HEq (fg.app (Fin.last (Word.append (leftBoundaryWord n)
      (Word.single .backward)).length)) (k.app 0) := by
    apply HEq.trans (ZigzagAppend.Moving.app_right_heq f g hj (Fin.last 1))
    exact (pushoutRightBoundaryInclusion_first (pushoutInput L R c) hc b hb).symm
  have hf : fg.app 0 = eqToHom
      ((ZigzagAppend.obj (leftBoundaryBlock L a ha) (BackwardZigzag.obj c hc.2)).first.trans
      (ZigzagAppend.obj (leftBoundaryBlock L a ha)
        (BackwardZigzag.obj (𝟙 (L.obj (Fin.last n)))
          ((weakEquivalences C).id_mem _))).first.symm) := by
    apply Zigzag.MovingHom.first_of_heq_id fg
    exact (ZigzagAppend.Moving.app_left_heq f g 0).trans (Zigzag.MovingHom.id_first _)
  exact ZigzagAppend.Moving.fixedMap fg k hj' hf
    (Zigzag.MovingHom.last_of_heq_id k
      (pushoutRightBoundaryInclusion_last (pushoutInput L R c) hc b hb))

end SerrePositivity.EInfinity.Hammock.MiddleBackward
