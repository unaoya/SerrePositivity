module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEndpoints

/-!
概要：同じ元の一単体を共通 Hom 解像の二つの実一単体で表す。
方針：標準三単体の (0,0,0,1) と (0,1,1,1) の係数へ元の一単体を制限する。
規約：元の一単体を変えず、逆向きの辺を選択しない。
使われ方：反転精密化の作用と元の右 Hom 作用を共通解像上で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 右射影が元の一単体、左射影が始点に定値となる実共通解像の係数。 -/
def edgewiseRefinementRightResolution {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X) _⦋1⦌ :=
  (edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) ≫
      SSet.yonedaEquiv.symm e

/-- 左射影が元の反転一単体、右射影が終点に定値となる実共通解像の係数。 -/
def edgewiseRefinementLeftResolution {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseSubdivision X) _⦋1⦌ :=
  (edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) ≫
      SSet.yonedaEquiv.symm e

/-- 右側の共通解像の係数の右射影は元の一単体そのもの。 -/
lemma edgewiseRefinementRightResolution_right {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseRight X).app (Opposite.op ⦋1⦌) (edgewiseRefinementRightResolution e) = e := by
  change SSet.yonedaEquiv (joinInr _ _ ≫ (edgewiseWeightIso 1).hom ≫
    stdSimplex.map (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) ≫
      SSet.yonedaEquiv.symm e) = e
  have h : SimplexCategory.mkHom (DGNerve.joinRightOrderHom 1 1) ≫
      (SimplexCategory.σ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2)) = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInr _ _), edgewiseWeightIso_inr,
    ← Category.assoc (stdSimplex.map _), ← stdSimplex.map_comp, h,
    CategoryTheory.Functor.map_id, Category.id_comp, Equiv.apply_symm_apply]

/-- 左側の共通解像の係数の左射影は元の反転一単体そのもの。 -/
lemma edgewiseRefinementLeftResolution_left {X : SSet.{u}} (e : X _⦋1⦌) :
    (edgewiseLeft X).app (Opposite.op ⦋1⦌) (edgewiseRefinementLeftResolution e) =
      SSet.opObjEquiv.symm e := by
  apply SSet.opObjEquiv.symm.injective
  change SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫ joinInl _ _ ≫
    (edgewiseWeightIso 1).hom ≫
      stdSimplex.map (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) ≫
        SSet.yonedaEquiv.symm e) = e
  have h : SimplexCategory.mkHom (DGNerve.joinLeftOrderHom 1 1) ≫
      (SimplexCategory.σ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2)) = 𝟙 ⦋1⦌ := by
    ext i
    fin_cases i <;> rfl
  rw [← Category.assoc (joinInl _ _), edgewiseWeightIso_inl, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc (stdSimplex.map _),
    ← stdSimplex.map_comp, h, CategoryTheory.Functor.map_id, Category.id_comp,
    Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
