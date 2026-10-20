module

public import SerrePositivity.EInfinity.Hammock.ForwardPathBoundaryComparisons

/-!
# 中央の backward 列を左ブロック全体の pullback で置換する

概要：元の X,Y を固定した全体の zigzag と、元の zigzag への縦弱同値を構成する。
方針：中央の弱同値 c≫p に対し、左ブロックを自明 fibration p で置換する。
規約：外側の元の backward 射も保持する。左右の forward 長は零でもよい。
使われ方：中央の列を自明 cofibration にする関手的置換の対象と counit 成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

abbrev word (n m : ℕ) : Word :=
  Word.append (Word.append (leftBoundaryWord n) (Word.single .backward)) (rightBoundaryWord m)

def obj (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ L.obj (Fin.last n)) (hu : weakEquivalences C u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    Zigzag (weakEquivalences C) (word n m) X Y :=
  ZigzagAppend.obj
    (ZigzagAppend.obj (leftBoundaryBlock L a ha) (BackwardZigzag.obj u hu))
    (rightBoundaryBlock R b hb)

lemma middle_weak (s : TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (u : R.obj 0 ⟶ s.right.obj (Fin.last n))
    (hu : weakEquivalences C u) (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u) :
    weakEquivalences C c := by
  apply (weakEquivalences C).of_postcomp _ s.hom hs.2
  exact h.symm ▸ hu

def pullbackObj (s : TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (a : s.right.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ s.right.obj (Fin.last n)) (hu : weakEquivalences C u)
    (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    Zigzag (weakEquivalences C) (word n m) X Y :=
  ZigzagAppend.obj
    (ZigzagAppend.obj (pullbackLeftBoundary s hs a ha)
      (BackwardZigzag.obj c (middle_weak s hs R u hu c h)))
    (rightBoundaryBlock R b hb)

def pullbackProjection (s : TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (a : s.right.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ s.right.obj (Fin.last n)) (hu : weakEquivalences C u)
    (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    Zigzag.Hom (pullbackObj s hs R a ha u hu c h b hb) (obj s.right R a ha u hu b hb) := by
  let f := pullbackLeftBoundaryProjection s hs a ha
  let g := BackwardZigzag.movingHom (middle_weak s hs R u hu c h) hu s.hom (𝟙 (R.obj 0))
    hs.2 ((weakEquivalences C).id_mem _) (h.trans (Category.id_comp u).symm)
  have hj : HEq (f.app (Fin.last (leftBoundaryWord n).length)) (g.app 0) :=
    pullbackLeftBoundaryProjection_last s hs a ha
  let fg := ZigzagAppend.Moving.map f g hj
  let k := Zigzag.MovingHom.id (rightBoundaryBlock R b hb)
  have hj' : HEq (fg.app (Fin.last (Word.append (leftBoundaryWord n)
      (Word.single .backward)).length)) (k.app 0) := by
    apply HEq.trans (ZigzagAppend.Moving.app_right_heq f g hj (Fin.last 1))
    exact (Zigzag.MovingHom.id_first (rightBoundaryBlock R b hb)).symm
  have hf : fg.app 0 = eqToHom
      ((ZigzagAppend.obj (pullbackLeftBoundary s hs a ha)
        (BackwardZigzag.obj c (middle_weak s hs R u hu c h))).first.trans
      (ZigzagAppend.obj (leftBoundaryBlock s.right a ha)
        (BackwardZigzag.obj u hu)).first.symm) := by
    apply Zigzag.MovingHom.first_of_heq_id fg
    exact (ZigzagAppend.Moving.app_left_heq f g 0).trans
      (pullbackLeftBoundaryProjection_first s hs a ha)
  exact ZigzagAppend.Moving.fixedMap fg k hj' hf
    (Zigzag.MovingHom.last_of_heq_id k (Zigzag.MovingHom.id_last _))

end SerrePositivity.EInfinity.Hammock.MiddleBackward
