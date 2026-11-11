module

public import SerrePositivity.KST.Spectra.SignedAdjointParametricInputEndpoints
public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：二つの実自然性区間から、全族二重 loop 入力の比較区間を実三角形付きで構成する。
方針：第二の区間を内部 Hom と交換へ移し、第一の区間の同じ後合成と合成する。
規約：入力 H 自身を仮定しない。使われ方：符号付き随伴の全族三正方形への実入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths
variable {P A A' Y Y' Z Z' : PointedSimplicialSet.{u}}
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ PointedObject.basedHom P A')
  (u : P ⟶ PointedObject.basedHom Y Y') (v : P ⟶ PointedObject.basedHom Z Z')
  (F : PointedMapping.VerticalPath
    (PointedObject.toPoint (PointedObject.basedHom P
      (PointedObject.basedHom CirclePower.space.{u} Y')))
    (f ≫ PointedMapping.parametricPost CirclePower.space.{u} u)
    (j ≫ PointedObject.basedHomMap P f'))
  (G : PointedMapping.VerticalPath
    (PointedObject.toPoint (PointedObject.basedHom P
      (PointedObject.basedHom CirclePower.space.{u} Z')))
    (g ≫ PointedMapping.parametricPost CirclePower.space.{u} v)
    (PointedMapping.transpose u ≫ PointedObject.basedHomMap P g'))

/-- 第二の実比較を同じ内部 Hom と交換に移し、元の第一入力へ制限する。 -/
def parametricInputComparisonFirst :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom P (doubleLoop Z')))
      (input f g ≫ doubleParametricPost v)
      ((f ≫ PointedMapping.parametricPost CirclePower.space.{u} u) ≫
        PointedObject.basedHomMap P (PointedObject.basedHomMap CirclePower.space.{u} g')) :=
  (((G.basedIhomMap CirclePower.space.{u}).pre f).basedPost
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} P
      (PointedObject.basedHom CirclePower.space.{u} Z')).hom).changeEndpoints
        (inputParametricFirst_start f g v).symm (inputParametricFirst_finish f g' u).symm

/-- 第一の実比較へ同じ第二入力を後合成し、元の合成入力の全族像へ進む。 -/
def parametricInputComparisonSecond :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom P (doubleLoop Z')))
      ((f ≫ PointedMapping.parametricPost CirclePower.space.{u} u) ≫
        PointedObject.basedHomMap P (PointedObject.basedHomMap CirclePower.space.{u} g'))
      (j ≫ PointedObject.basedHomMap P (input f' g')) := by
  refine (F.basedPost (PointedObject.basedHomMap P
    (PointedObject.basedHomMap CirclePower.space.{u} g'))).changeEndpoints rfl ?_
  have hm : PointedObject.basedHomMap P (input f' g') =
      PointedObject.basedHomMap P f' ≫
        PointedObject.basedHomMap P (PointedObject.basedHomMap CirclePower.space.{u} g') :=
    CategoryTheory.Functor.map_comp (ihom P) _ _
  rw [hm]
  exact (Category.assoc _ _ _).symm

variable [KanComplex Z'.right]
local instance parametricInputComparisonInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance parametricInputComparisonDoubleKan : KanComplex (doubleLoop Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance parametricInputComparisonParameterKan :
    KanComplex (PointedObject.basedHom P (doubleLoop Z')).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の二実比較区間と同じ合成三角形を保持する、全族入力の比較。 -/
def parametricInputComparisonComposite :
    PointedMapping.BasedPathComposite (parametricInputComparisonFirst f g g' u v G)
      (parametricInputComparisonSecond f f' g' j u F) :=
  PointedMapping.BasedPathComposite.choose (parametricInputComparisonFirst f g g' u v G)
    (parametricInputComparisonSecond f f' g' j u F)

/-- 二つの実自然性区間から構成した、三正方形に共通して使う同じ全族実入力。 -/
def parametricInputComparison :
    PointedMapping.VerticalPath
      (PointedObject.toPoint (PointedObject.basedHom P (doubleLoop Z')))
      (input f g ≫ doubleParametricPost v) (j ≫ PointedObject.basedHomMap P (input f' g')) :=
  (parametricInputComparisonComposite f g f' g' j u v F G).path

/-- 合成三角形の第一面は、元の第二比較区間の同じ内部 Hom・交換像。 -/
lemma parametricInputComparisonComposite_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (parametricInputComparisonComposite f g f' g' j u v F G).triangle.simplex =
        (parametricInputComparisonFirst f g g' u v G).path := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 第二面も、元の第一比較区間への同じ後合成像。 -/
lemma parametricInputComparisonComposite_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (parametricInputComparisonComposite f g f' g' j u v F G).triangle.simplex =
        (parametricInputComparisonSecond f f' g' j u F).path := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.Spectra.SignedAdjointPaths
