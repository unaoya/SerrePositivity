module

public import SerrePositivity.EInfinity.Hammock.RelativeColimitMap

/-!
# Hom の宇宙が異なる相対関手による元の hammock 写像

概要：対象の宇宙を保ち、Hom の宇宙を下げる元の相対関手を全単体へ適用する。
方針：全語の nerve 単体を直接送り、元の余極限と正規化を使用する。
規約：元の全語・全単体作用素・全標準射を保持する。
使われ方：cofibrant 包含と HomLift を通る既存比較の作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.MixedRelative
open CategoryTheory CategoryTheory.Limits
variable {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (X Y : C)

def graphMap (w : Word) : graph W w X Y ⟶
    graph V w (F.functor.obj X) (F.functor.obj Y) where
  app _ := ↾fun σ => σ ⋙ Zigzag.Relative.functor F
  naturality _ _ _ := rfl

def graphDiagramMap : graphDiagram W X Y ⟶
    graphDiagram V (F.functor.obj X) (F.functor.obj Y) where
  app w := graphMap F X Y w
  naturality a b f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro σ
    change σ ⋙ (WordAction.functor f ⋙ Zigzag.Relative.functor F) =
      σ ⋙ (Zigzag.Relative.functor F ⋙ WordAction.functor f)
    exact congrArg (fun H => σ ⋙ H) (Zigzag.Relative.wordAction_functor_eq F f).symm

def colimitMap : colimitGraph W X Y ⟶
    colimitGraph V (F.functor.obj X) (F.functor.obj Y) :=
  colim.map (graphDiagramMap F X Y)

lemma graphInclusion_colimitMap (w : Word) :
    graphInclusion W X Y w ≫ colimitMap F X Y =
      graphMap F X Y w ≫ graphInclusion V (F.functor.obj X) (F.functor.obj Y) w :=
  colimit.ι_map _ _

def reducedMap : reducedSimplicialSet W X Y ⟶
    reducedSimplicialSet V (F.functor.obj X) (F.functor.obj Y) :=
  (reducedColimitIso W X Y).inv ≫ colimitMap F X Y ≫
    (reducedColimitIso V (F.functor.obj X) (F.functor.obj Y)).hom

lemma reducedColimitIso_map : (reducedColimitIso W X Y).hom ≫ reducedMap F X Y =
    colimitMap F X Y ≫ (reducedColimitIso V (F.functor.obj X) (F.functor.obj Y)).hom := by
  simp only [reducedMap, Iso.hom_inv_id_assoc]

lemma graphNormalization_reducedMap (w : Word) :
    graphNormalization W X Y w ≫ reducedMap F X Y =
      graphMap F X Y w ≫ graphNormalization V (F.functor.obj X) (F.functor.obj Y) w := by
  rw [← reducedColimitIso_hom_fac W X Y w, Category.assoc, reducedColimitIso_map,
    ← Category.assoc, graphInclusion_colimitMap, Category.assoc, reducedColimitIso_hom_fac]

end SerrePositivity.EInfinity.Hammock.MixedRelative
