module

public import SerrePositivity.KST.Spectra.UnbasedPathFamilies
public import SerrePositivity.KST.Spectra.FreeMappingPointedIso

/-!
概要：通常の写像空間の頂点表示を自由基点付き Hom の頂点表示と同定する。
方針：curry と Yoneda の自然性、元の成分への制限を計算する。
規約：源や係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。path 延長の終点の実際の fiber 頂点との比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 定数射の頂点表示は通常の写像空間の指定基点。 -/
@[simp]
lemma mapVertex_const (A : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    mapVertex Y (SSet.const (X := A) Y.basepoint) = (obj A Y).basepoint := by
  apply SSet.yonedaEquiv.symm.injective
  rw [mapVertex, Equiv.symm_apply_apply, SSet.yonedaEquiv_symm_zero]
  apply uncurry_injective
  rw [uncurry_curry, uncurry_constant_basepoint, comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]

/-- 通常の射の頂点表示は源への制限と可換。 -/
lemma mapVertex_pre {A B : SSet.{u}} (i : A ⟶ B) (Y : PointedSimplicialSet.{u})
    (f : B ⟶ Y.right) :
    (pre i Y).right.app _ (mapVertex Y f) = mapVertex Y (i ≫ f) := by
  change ((MonoidalClosed.pre i).app Y.right).app _
    (SSet.yonedaEquiv (curry (fst B (Δ[0] : SSet.{u}) ≫ f))) = _
  rw [← SSet.yonedaEquiv_comp, curry_pre_app, whiskerRight_fst_assoc]
  rfl

/-- 概要：自由基点付き射の頂点を通常の写像空間へ制限すると元の射の頂点になる。
方針：点つきパラメータ族の包含と元の成分の制限を curry の自然性で計算する。
規約：二つの頂点表示を選び直さずに厳密に照合する。
使われ方：Goerss–Jardine VIII §1。相対商の fiber 頂点の包含の計算。 -/
lemma freeHomIso_familyVertex {A : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : A ⟶ Y.right) :
    (freeHomIso A Y).hom.right.app _
        (PointedMapping.familyVertex ((PointedObject.adjoinHomEquiv A Y).symm f)) =
      mapVertex Y f := by
  change (FreePointedHomRestriction.restrict A Y).app _
    (SSet.yonedaEquiv (PointedMapping.pointFamily _)) = _
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv _ = SSet.yonedaEquiv (curry (fst A (Δ[0] : SSet.{u}) ≫ f))
  apply congrArg SSet.yonedaEquiv
  dsimp only [PointedMapping.pointFamily, FreePointedHomRestriction.restrict]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, curry_pre_app, whiskerRight_fst_assoc]
  change curry (fst A (Δ[0] : SSet.{u}) ≫
    (PointedObject.adjoinHomEquiv A Y) ((PointedObject.adjoinHomEquiv A Y).symm f)) = _
  rw [Equiv.apply_symm_apply]

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
