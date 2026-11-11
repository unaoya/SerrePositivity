module
public import SerrePositivity.KST.SConstruction.MonicKPrismCompositeCylinderTransport
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition

/-! # 元の定数段族と後続適合円柱の実合成
概要：後続適合円柱を元の段族で前合成した式を、同じ源の通常の制限へ同定する。
方針：元の段族の定数性と suspension の頂点作用、豊穣合成の単位則を使う。
規約：実円柱の全時刻の等号であり、補正済み段族に置き換えない。
使われ方：元の全比較三角形の第二面と保存済み二次元補正の始点の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping SerrePositivity.InfinityCategories
open scoped Simplicial
local instance originalCompatibilityCylinderPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の段族との実合成は、元の同じ段の suspension による通常の前合成。 -/
lemma monicKPrismCompositeCompatibilityAt_raw (n : ℕ) :
    monicKPrismCompositeCompatibilityAt F f g n (monicKPrismRawLevelFamily n F f) =
      (monicKPrismCompositeCompatibility F f g n).h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) n)
          ((kKanSequence (F.obj z)).level (n + 1)).space := by
  let a : ((kOmegaSpectrum (F.obj x)).level n).space ⟶
      ((kKanSequence (F.obj y)).level n).space := monicKToRawLevelMap (F.map f) n
  have hs : (suspensionHom ((kOmegaSpectrum (F.obj x)).level n).space
      ((kKanSequence (F.obj y)).level n).space).right.app (Opposite.op ⦋0⦌)
      (familyVertex a) = familyVertex (PointedSimplicialSet.circle.{u} ◁ a) := by
    rw [familyVertex_eq_pointedHomVertex, familyVertex_eq_pointedHomVertex]
    exact pointedHomVertexEquiv_suspension a
  change lift (_ ≫ SSet.const (familyVertex a) ≫ (suspensionHom _ _).right) _ ≫ _ =
    (monicKPrismCompositeCompatibility F f g n).h ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (PointedSimplicialSet.circle.{u} ◁ a)
        ((kKanSequence (F.obj z)).level (n + 1)).space
  simp only [SSet.const_comp, SSet.comp_const, hs]
  exact pointedFamilyComposition_const_left _ _

end SerrePositivity.KST.SConstruction
