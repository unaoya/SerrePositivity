module

public import SerrePositivity.KST.Spectra.SignedAdjointCompositionPaths
public import SerrePositivity.KST.Spectra.PointedBasedPathComposition

/-!
概要：二つの随伴入力の実比較区間から、合成した二重 loop 入力の比較を構成する。
方針：第二の比較へ内部 Hom を作用させ、第一の比較の後合成と実三角形付きで合成する。
規約：随伴入力の厳密自然性を要求しない。使われ方：単位構造の二辺に共通の入力比較。
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
variable {A A' Y Y' Z Z' : PointedSimplicialSet.{u}}
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)
  (f' : A' ⟶ PointedObject.basedHom CirclePower.space.{u} Y')
  (g' : Y' ⟶ PointedObject.basedHom CirclePower.space.{u} Z')
  (j : A ⟶ A') (u : Y ⟶ Y') (v : Z ⟶ Z')
  (F : PointedMapping.VerticalPath
    (PointedObject.toPoint (PointedObject.basedHom CirclePower.space.{u} Y'))
    (f ≫ PointedObject.basedHomMap CirclePower.space.{u} u) (j ≫ f'))
  (G : PointedMapping.VerticalPath
    (PointedObject.toPoint (PointedObject.basedHom CirclePower.space.{u} Z'))
    (g ≫ PointedObject.basedHomMap CirclePower.space.{u} v) (u ≫ g'))

/-- 第二の実入力比較を内部 Hom に移し、元の第一入力へ制限した同じ区間。 -/
def inputComparisonFirst :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Z'))
      (input f g ≫ doublePost v) (f ≫ (ihom CirclePower.space.{u}).map (u ≫ g')) := by
  refine ((G.basedIhomMap CirclePower.space.{u}).pre f).changeEndpoints ?_ rfl
  change (f ≫ (ihom CirclePower.space.{u}).map g) ≫
      (ihom CirclePower.space.{u}).map (PointedObject.basedHomMap CirclePower.space.{u} v) = _
  rw [Category.assoc, ← Functor.map_comp]

/-- 第一の実入力比較に同じ第二入力を後合成し、同じ中間辺から元の合成入力へ進む。 -/
def inputComparisonSecond :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Z'))
      (f ≫ (ihom CirclePower.space.{u}).map (u ≫ g')) (j ≫ input f' g') := by
  refine (F.basedPost (PointedObject.basedHomMap CirclePower.space.{u} g')).changeEndpoints ?_ ?_
  · change f ≫ (ihom CirclePower.space.{u}).map (u ≫ g') =
      (f ≫ (ihom CirclePower.space.{u}).map u) ≫ (ihom CirclePower.space.{u}).map g'
    rw [Functor.map_comp, Category.assoc]
  · exact (Category.assoc j f' (PointedObject.basedHomMap CirclePower.space.{u} g')).symm

variable [KanComplex Z'.right]
local instance inputComparisonInnerKan :
    KanComplex (PointedObject.basedHom CirclePower.space.{u} Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
local instance inputComparisonDoubleKan : KanComplex (doubleLoop Z').right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の二つの入力比較区間と同じ実合成三角形を保持する、二重 loop 入力比較。 -/
def inputComparisonComposite :
    PointedMapping.BasedPathComposite (inputComparisonFirst f g g' u v G)
      (inputComparisonSecond f f' g' j u F) :=
  PointedMapping.BasedPathComposite.choose (inputComparisonFirst f g g' u v G)
    (inputComparisonSecond f f' g' j u F)

/-- 両方の随伴入力の実比較から得た、二辺に共通して使う同じ実入力区間。 -/
def inputComparison :
    PointedMapping.VerticalPath (PointedObject.toPoint (doubleLoop Z'))
      (input f g ≫ doublePost v) (j ≫ input f' g') :=
  (inputComparisonComposite f g f' g' j u v F G).path

/-- 比較三角形の第一辺は、元の第二入力比較の同じ内部 Hom 像。 -/
lemma inputComparisonComposite_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (inputComparisonComposite f g f' g' j u v F G).triangle.simplex =
        (inputComparisonFirst f g g' u v G).path := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 比較三角形の第二辺も、元の第一入力比較の同じ後合成像。 -/
lemma inputComparisonComposite_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (inputComparisonComposite f g f' g' j u v F G).triangle.simplex =
        (inputComparisonSecond f f' g' j u F).path := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

end SerrePositivity.KST.Spectra.SignedAdjointPaths
