module

public import SerrePositivity.KST.Spectra.SignedAdjointCompositionPaths
public import SerrePositivity.KST.Spectra.PointedBasedPathDifference
public import SerrePositivity.KST.Spectra.PointedVerticalPathComposition

/-!
概要：符号付き随伴比較の元の二辺と、合成・逆向きの二つの実三角形を保持する。
方針：二辺を固定した内ホーンと、定数辺を固定した外ホーンを充填する。
規約：成分の等式から区間を選び直さない。使われ方：単位構造区間の具体的な入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
variable {A Y Z W : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex W.right]
  (a : Z ⟶ PointedObject.basedHom PointedSimplicialSet.circle.{u} W)
  (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right)
  (f : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y)
  (g : Y ⟶ PointedObject.basedHom CirclePower.space.{u} Z)

local instance signedTriangleTargetKan : KanComplex (target Z).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の交換符号辺と二重反転辺をそのまま保持する、実際の合成三角形。 -/
def forwardComposite : PointedMapping.BasedPathComposite (firstPath a ha f g) (secondPath f g) :=
  PointedMapping.BasedPathComposite.choose (firstPath a ha f g) (secondPath f g)

/-- 合成辺と同じ始点の定数辺を固定し、逆向きの辺とその三角形を選ぶ。 -/
def reverseComposite :
    PointedMapping.BasedPathDifference (forwardComposite a ha f g).path
      (PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z)) (left f g)) :=
  PointedMapping.BasedPathDifference.choose (forwardComposite a ha f g).path
    (PointedMapping.VerticalPath.refl (PointedObject.toPoint (target Z)) (left f g))

/-- 合成三角形の第一辺は元の交換符号の同じ実区間。 -/
lemma forwardComposite_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (forwardComposite a ha f g).triangle.simplex = (firstPath a ha f g).path := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 合成三角形の第二辺は同じ自然な二重反転の実区間。 -/
lemma forwardComposite_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (forwardComposite a ha f g).triangle.simplex = (secondPath f g).path := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 合成三角形の対角辺も、同じ充填で得た実際の合成区間そのもの。 -/
lemma forwardComposite_one :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (forwardComposite a ha f g).triangle.simplex = (forwardComposite a ha f g).path.path := by
  rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  exact Equiv.symm_apply_apply _ _

/-- 逆向き三角形の第一辺は同じ合成区間全体を保持する。 -/
lemma reverseComposite_two :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (reverseComposite a ha f g).triangle.simplex = (forwardComposite a ha f g).path.path :=
  PointedMapping.BasedPathDifference.triangle_two _

/-- 逆向き三角形の第二辺は、同じ逆向きの実区間そのもの。 -/
lemma reverseComposite_zero :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (reverseComposite a ha f g).triangle.simplex = (reverseComposite a ha f g).path.path :=
  PointedMapping.BasedPathDifference.triangle_zero _

/-- 逆向き三角形の対角辺は元の同じ始点で一定。 -/
lemma reverseComposite_one :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm
      (reverseComposite a ha f g).triangle.simplex = SSet.const (PointedMapping.familyVertex
        (left f g)) :=
  PointedMapping.BasedPathDifference.triangle_one _

end SerrePositivity.KST.Spectra.SignedAdjointPaths
