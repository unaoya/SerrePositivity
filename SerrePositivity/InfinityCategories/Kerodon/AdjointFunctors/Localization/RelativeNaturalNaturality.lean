module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalFunctors
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendSquare
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomFixed

/-!
# 固定端点の相対自然変換の全縦射での自然性

概要：元の成分を外側の二列と貼った比較は元の全縦射に自然である。
方針：中間の自然性と外側の恒等縦射の四角形を二回貼る。
規約：接合点にある元の自然変換の成分を保持する。
使われ方：元の固定語の nerve ホモトピー。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma component_naturality {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeFunctor η w X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.component η hη T =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.component η hη S ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterFunctor η w X Y).map f := by
  let bf := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F f)
  let bg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map G f)
  let ir := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (η.app Y))
  let jr := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (𝟙 (G.functor.obj Y)))
  have hbf : HEq (bf.app (Fin.last w.length)) (ir.app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F f)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first _).symm
  have hbg : HEq (bg.app (Fin.last w.length)) (jr.app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map G f)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first _).symm
  let mf := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map bf ir hbf
  let mg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map bg jr hbg
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_naturality η hη f
  have hr : ir.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y).comp jr := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change 𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y).app j = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y).app j ≫ 𝟙 _
    simp
  have hi : mf.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη T) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη S).comp mg :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_square bf ir bg jr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom η hη T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.rightEdge η hη Y)
      hbf hbg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalMoving.movingHom_last η hη T) hs hr
  let il := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (𝟙 (F.functor.obj X)))
  let jl := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (η.app X))
  have hmf : HEq (il.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length)) (mf.app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last _).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq bf ir 0).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_first (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map F f))).symm
  have hmg : HEq (jl.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward).length)) (mg.app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last _).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq bg jr 0).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_first (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.map G f))).symm
  have hl : il.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X).comp jl := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    change 𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X).app j = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X).app j ≫ 𝟙 _
    simp
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_square il mf jl mg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.leftEdge η hη X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom η hη T)
    hmf hmg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom_first η hη S).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeNaturalRows.innerHom_first η hη T).symm hl hi
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  exact congrArg (fun k => k.app j) h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
