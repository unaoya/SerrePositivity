module
public import SerrePositivity.KST.SConstruction.PointedComponentPiIsomorphism
public import SerrePositivity.KST.Spectra.PointedCurryingParameterComponents
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-! # 基点固定の実比較四角形による Ω 条件の検出
概要：元の組み立て随伴と前向き弱比較から、同じ新構造射の随伴の全基点 π 同型を得る。
方針：実成分の等号を curry し、loop の弱比較保存と局所化の合成消去を使う。
規約：逆射の coherent な選択は不要。使われ方：再帰 BF 列の全 Ω 条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.SimplicialModel

/-- 同じ circle 内部 Hom の元の Kan 性を、閉構造の対象の型でも保持する。 -/
local instance pointedCylinderOmegaLoop_kanComplex (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] :
    KanComplex ((ihom PointedSimplicialSet.circle.{u}).obj Y).right :=
  loopSpace_kanComplex Y

/-- 元の評価の点つき成分を回収する最初の構造射は Ω 条件を満たす。 -/
lemma evaluationCylinderAdjoint_piIsomorphism
    {Z T : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex T.right]
    (c : Z ⟶ T) (hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right) (σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) ⟶ T)
    (hσ : componentOf σ = componentOf ((ihom.ev PointedSimplicialSet.circle.{u}).app Z ≫ c)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry σ).right := by
  have h := componentOf_curry hσ
  have he : curry ((ihom.ev PointedSimplicialSet.circle.{u}).app Z ≫ c) =
      (ihom PointedSimplicialSet.circle.{u}).map c := by
    rw [curry_natural_right, ← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]
  exact kanPiIsomorphism_of_pointed_component _ _
    (h.trans (congrArg componentOf he))
    (post_piIsomorphism PointedSimplicialSet.circle c hc)

/-- 元の組み立てと実基点固定で可換な弱比較四角形は、新構造射の Ω 条件を与える。 -/
lemma cylinderAssemblyAdjoint_piIsomorphism
    {U K B T : PointedSimplicialSet.{u}} [KanComplex U.right] [KanComplex K.right]
    [KanComplex B.right] [KanComplex T.right]
    (l : U ⟶ K) (hl : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism l.right)
    (a : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension U ⟶ B) (ha : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry a).right)
    (c : B ⟶ T) (hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right) (σ : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension K ⟶ T)
    (hσ : componentOf (PointedSimplicialSet.circle.{u} ◁ l ≫ σ) = componentOf (a ≫ c)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (curry σ).right := by
  have h := componentOf_curry hσ
  rw [curry_natural_left, curry_natural_right] at h
  have hp := kanPiIsomorphism_of_pointed_component _ _ h
    (ha.comp (post_piIsomorphism PointedSimplicialSet.circle c hc))
  let Q := AnodyneHomotopy.anodyneQ
  let _ : IsIso (Q.map l.right) := pointed_localized_isIso_of_piIsomorphism l hl
  have hq := pointed_localized_isIso_of_piIsomorphism (l ≫ curry σ) hp
  have hq' : IsIso (Q.map l.right ≫ Q.map (curry σ).right) := by
    rw [← Q.map_comp]
    exact hq
  exact kanPiIsomorphism_of_localized_isIso (curry σ).right
    ((isIso_comp_left_iff _ _).mp hq')

end SerrePositivity.KST.SConstruction
