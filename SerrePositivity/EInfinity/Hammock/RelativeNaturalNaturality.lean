module

public import SerrePositivity.EInfinity.Hammock.RelativeNaturalFunctors
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendSquare
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingHomFixed

/-!
# 固定端点の相対自然変換の全縦射での自然性

概要：元の成分を外側の二列と貼った比較は元の全縦射に自然である。
方針：中間の自然性と外側の恒等縦射の四角形を二回貼る。
規約：接合点にある元の自然変換の成分を保持する。
使われ方：元の固定語の nerve ホモトピー。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {w : Word} {X Y : C}

lemma component_naturality {S T : Zigzag W w X Y} (f : S ⟶ T) :
    (beforeFunctor η w X Y).map f ≫ component η hη T =
      component η hη S ≫ (afterFunctor η w X Y).map f := by
  let bf := Zigzag.MovingHom.ofHom (Zigzag.Relative.map F f)
  let bg := Zigzag.MovingHom.ofHom (Zigzag.Relative.map G f)
  let ir := Zigzag.MovingHom.id (ForwardZigzag.obj (W := V) (η.app Y))
  let jr := Zigzag.MovingHom.id (ForwardZigzag.obj (W := V) (𝟙 (G.functor.obj Y)))
  have hbf : HEq (bf.app (Fin.last w.length)) (ir.app 0) :=
    (Zigzag.MovingHom.ofHom_last (Zigzag.Relative.map F f)).trans
      (Zigzag.MovingHom.id_first _).symm
  have hbg : HEq (bg.app (Fin.last w.length)) (jr.app 0) :=
    (Zigzag.MovingHom.ofHom_last (Zigzag.Relative.map G f)).trans
      (Zigzag.MovingHom.id_first _).symm
  let mf := ZigzagAppend.Moving.map bf ir hbf
  let mg := ZigzagAppend.Moving.map bg jr hbg
  have hs := movingHom_naturality η hη f
  have hr : ir.comp (rightEdge η hη Y) = (rightEdge η hη Y).comp jr := by
    apply Zigzag.MovingHom.ext
    intro j
    change 𝟙 _ ≫ (rightEdge η hη Y).app j = (rightEdge η hη Y).app j ≫ 𝟙 _
    simp
  have hi : mf.comp (innerHom η hη T) = (innerHom η hη S).comp mg :=
    ZigzagAppend.Moving.map_square bf ir bg jr
      (movingHom η hη S) (rightEdge η hη Y)
      (movingHom η hη T) (rightEdge η hη Y)
      hbf hbg (movingHom_last η hη S) (movingHom_last η hη T) hs hr
  let il := Zigzag.MovingHom.id (ForwardZigzag.obj (W := V) (𝟙 (F.functor.obj X)))
  let jl := Zigzag.MovingHom.id (ForwardZigzag.obj (W := V) (η.app X))
  have hmf : HEq (il.app (Fin.last (Word.single .forward).length)) (mf.app 0) :=
    (Zigzag.MovingHom.id_last _).trans
      ((ZigzagAppend.Moving.app_left_heq bf ir 0).trans
        (Zigzag.MovingHom.ofHom_first (Zigzag.Relative.map F f))).symm
  have hmg : HEq (jl.app (Fin.last (Word.single .forward).length)) (mg.app 0) :=
    (Zigzag.MovingHom.id_last _).trans
      ((ZigzagAppend.Moving.app_left_heq bg jr 0).trans
        (Zigzag.MovingHom.ofHom_first (Zigzag.Relative.map G f))).symm
  have hl : il.comp (leftEdge η hη X) = (leftEdge η hη X).comp jl := by
    apply Zigzag.MovingHom.ext
    intro j
    change 𝟙 _ ≫ (leftEdge η hη X).app j = (leftEdge η hη X).app j ≫ 𝟙 _
    simp
  have h := ZigzagAppend.Moving.map_square il mf jl mg
    (leftEdge η hη X) (innerHom η hη S) (leftEdge η hη X) (innerHom η hη T)
    hmf hmg (innerHom_first η hη S).symm (innerHom_first η hη T).symm hl hi
  apply Zigzag.hom_ext
  intro j
  exact congrArg (fun k => k.app j) h

end SerrePositivity.EInfinity.Hammock.RelativeNatural
