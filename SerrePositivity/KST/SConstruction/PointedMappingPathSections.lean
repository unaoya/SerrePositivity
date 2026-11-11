module
public import SerrePositivity.KST.SConstruction.PointedLiftSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead

/-! # mapping path 切断による逆射の選択空間
概要：点つき Kan 同値の逆射を可縮な切断空間の頂点から構成する。
方針：mapping path の終点射への持ち上げを取り、源へ射影する。
規約：任意の選択頂点で両方向の基点固定ホモトピーを証明する。
使われ方：比較逆射の高次選択を Kan 延長と同じ形で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- mapping path の終点射の切断の空間。 -/
def pointedMappingPathSectionSpace {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pointedLiftSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f) (𝟙 Y)

/-- 全基点 π 同型の mapping path 切断の空間は可縮 Kan。 -/
lemma pointedMappingPathSectionSpace_isContractibleKan {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointedMappingPathSectionSpace f) :=
  pointedLiftSpace_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f hf) _

/-- 切断の選択頂点が与える実際の逆向きの射。 -/
def pointedMappingPathInverseAt {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (v : (pointedMappingPathSectionSpace f) _⦋0⦌) : Y ⟶ X :=
  pointedLiftMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f) (𝟙 Y) v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f

/-- 切断の全パラメーターを逆向きの写像空間に移す実際の射。 -/
def pointedMappingPathInverseFamily {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    pointedMappingPathSectionSpace f ⟶ (PointedObject.basedHom Y X).right :=
  pullback.fst (PointedObject.basedHomMap Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f)).right
    (SSet.yonedaEquiv.symm (PointedMapping.familyVertex (𝟙 Y))) ≫
      (PointedObject.basedHomMap Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f)).right

/-- 逆向きのパラメーター族は各頂点で構成済みの逆射を回収する。 -/
lemma pointedMappingPathInverseFamily_vertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (v : (pointedMappingPathSectionSpace f) _⦋0⦌) :
    (pointedMappingPathInverseFamily f).app (Opposite.op ⦋0⦌) v =
      PointedMapping.familyVertex (pointedMappingPathInverseAt f v) := by
  let a := (pullback.fst (PointedObject.basedHomMap Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f)).right
    (SSet.yonedaEquiv.symm (PointedMapping.familyVertex (𝟙 Y)))).app (Opposite.op ⦋0⦌) v
  have ha : a = PointedMapping.familyVertex (pointedLiftMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f) (𝟙 Y) v) :=
    (PointedMapping.familyVertex_familyMap Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f) a).symm
  exact (congrArg ((PointedObject.basedHomMap Y (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f)).right.app
    (Opposite.op ⦋0⦌)) ha).trans (PointedMapping.familyVertex_post _ _)

/-- 任意の切断選択は実際の基点固定ホモトピー逆を与える。 -/
lemma pointedMappingPathInverseAt_homotopy {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right)
    (v : (pointedMappingPathSectionSpace f) _⦋0⦌) :
    (∃ H : SSet.Homotopy (𝟙 X.right) (f ≫ pointedMappingPathInverseAt f v).right,
      X.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) ∧
    (∃ H : SSet.Homotopy (𝟙 Y.right) (pointedMappingPathInverseAt f v ≫ f).right,
      Y.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom) := by
  let p := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f
  let r := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f
  let u := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f
  let s := pointedLiftMap p (𝟙 Y) v
  have hs : s ≫ p = 𝟙 Y := pointedLiftMap_fac p (𝟙 Y) v
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f hf
  have hr := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction_rlp f
  have hup : u ≫ p = f := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_projection f
  have hur : u ≫ r = 𝟙 X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction f
  have hX : u ≫ p = (f ≫ s) ≫ p := by rw [Category.assoc, hs, Category.comp_id, hup]
  have hY : s ≫ r = (pointedMappingPathInverseAt f v ≫ u) ≫ r := by
    rw [Category.assoc, hur, Category.comp_id]
    rfl
  obtain ⟨HX, hHX⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopy_of_comp_eq p hp u (f ≫ s) hX
  obtain ⟨HY, hHY⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopy_of_comp_eq r hr s
    (pointedMappingPathInverseAt f v ≫ u) hY
  constructor
  · let H : SSet.Homotopy (𝟙 X.right) (f ≫ pointedMappingPathInverseAt f v).right := {
      h := HX.h ≫ r.right
      h₀ := by rw [← Category.assoc, HX.h₀]; exact congrArg Under.Hom.right hur
      h₁ := by rw [← Category.assoc, HX.h₁]; rfl
      rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
    refine ⟨H, ?_⟩
    change X.hom ▷ (Δ[1] : SSet.{u}) ≫ (HX.h ≫ r.right) = _
    rw [← Category.assoc, hHX, Category.assoc, Under.w r]
  · let H : SSet.Homotopy (𝟙 Y.right) (pointedMappingPathInverseAt f v ≫ f).right := {
      h := HY.h ≫ p.right
      h₀ := by rw [← Category.assoc, HY.h₀]; exact congrArg Under.Hom.right hs
      h₁ := by
        rw [← Category.assoc, HY.h₁]
        exact congrArg Under.Hom.right
          ((Category.assoc _ u p).trans (congrArg (pointedMappingPathInverseAt f v ≫ ·) hup))
      rel := by ext m ⟨⟨z, hz⟩, t⟩; exact hz.elim }
    refine ⟨H, ?_⟩
    change Y.hom ▷ (Δ[1] : SSet.{u}) ≫ (HY.h ≫ p.right) = _
    rw [← Category.assoc, hHY, Category.assoc, Under.w p]

/-- 切断の高次選択は任意の単射に沿い既存の選択を保って補完できる。 -/
lemma pointedMappingPathSectionSpace_relative_lifting {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ pointedMappingPathSectionSpace f) :
    ∃ b : T ⟶ pointedMappingPathSectionSpace f, j ≫ b = a :=
  pointedLiftSpace_relative_lifting _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f hf) _ j a

end SerrePositivity.KST.SConstruction
