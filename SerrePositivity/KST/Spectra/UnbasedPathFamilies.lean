module

public import SerrePositivity.KST.Spectra.RestrictionBoundaryFamilies
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism
public import SerrePositivity.KST.Comparison.BasedPathEndpoint

/-!
概要：源上の path の族を通常の写像空間の辺へ転置し、両端を計算する。
方針：区間と源を交換して curry し、始点の固定条件と通常の終点評価を使う。
規約：頂点零は定数写像、頂点一は path の終点の族。
使われ方：Goerss–Jardine VIII §1。path 延長の終点を実際の接続写像へ移す。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 源からの通常の射を、定数な零次パラメータを持つ写像空間の頂点で表す。 -/
def mapVertex {A : SSet.{u}} (Y : PointedSimplicialSet.{u}) (f : A ⟶ Y.right) :
    (obj A Y).right _⦋0⦌ := yonedaEquiv (curry (fst A (Δ[0] : SSet.{u}) ≫ f))

/-- path の族を通常の写像空間の辺へ転置する。 -/
def pathFamilyEdge {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : A ⟶ (basedPathSpace Y).right) : (Δ[1] : SSet.{u}) ⟶ (obj A Y).right :=
  curry ((β_ A (Δ[1] : SSet.{u})).hom ≫
    uncurry (H ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y))

/-- path の族の辺の頂点一は終点の族。 -/
lemma pathFamilyEdge_face_zero {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : A ⟶ (basedPathSpace Y).right) :
    stdSimplex.δ (0 : Fin 2) ≫ pathFamilyEdge Y H =
      yonedaEquiv.symm (mapVertex Y (H ≫ (pathEndpoint Y).right)) := by
  have he : H ≫ (pathEndpoint Y).right =
      (λ_ A).inv ≫ KanPath.endpoint 1 ▷ A ≫
        uncurry (H ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y) := by
    rw [Comparison.basedPathEndpoint_evaluation, ← Category.assoc]
    have hh := KanPath.curry_evaluation
      (uncurry (H ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)) (1 : Fin 2)
    rw [curry_uncurry] at hh
    exact hh
  have hp : A ◁ stdSimplex.δ (0 : Fin 2) ≫ (β_ A (Δ[1] : SSet.{u})).hom =
      fst A (Δ[0] : SSet.{u}) ≫ (λ_ A).inv ≫ KanPath.endpoint 1 ▷ A := by
    rw [stdSimplex.δ_zero_eq_const]
    rfl
  rw [pathFamilyEdge, mapVertex, Equiv.symm_apply_apply, ← curry_natural_left, he]
  have hh := congrArg (fun t ↦ curry
    (t ≫ uncurry (H ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y))) hp
  simp only [Category.assoc] at hh ⊢
  exact hh

/-- path の族の辺の頂点零は基点への定数写像。 -/
lemma pathFamilyEdge_face_one {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (H : A ⟶ (basedPathSpace Y).right) :
    stdSimplex.δ (1 : Fin 2) ≫ pathFamilyEdge Y H = SSet.const (obj A Y).basepoint := by
  have hp : A ◁ stdSimplex.δ (1 : Fin 2) ≫ (β_ A (Δ[1] : SSet.{u})).hom =
      fst A (Δ[0] : SSet.{u}) ≫ (λ_ A).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.hom ▷ A := by
    rw [stdSimplex.δ_one_eq_const]
    rfl
  rw [pathFamilyEdge, ← curry_natural_left]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_constant_basepoint]
  rw [← Category.assoc, hp]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
  simp only [comp_toUnit_assoc]

/-- path の族の転置は源への制限と可換。 -/
@[reassoc]
lemma pathFamilyEdge_pre {A B : SSet.{u}} (i : A ⟶ B) (Y : PointedSimplicialSet.{u})
    (H : B ⟶ (basedPathSpace Y).right) :
    pathFamilyEdge Y H ≫ (pre i Y).right = pathFamilyEdge Y (i ≫ H) := by
  change curry _ ≫ (MonoidalClosed.pre i).app Y.right = curry _
  rw [curry_pre_app]
  apply congrArg curry
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ (β_ A (Δ[1] : SSet.{u})).hom ≫ t)
    (uncurry_natural_left i (H ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).symm

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
