module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeUnitInputModelPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.CompositionInputTriangleExt
/-! # 元入力付き単位補正道の厳密な端点

概要：四補正道の元端と共通補正端を、三角形全体と元 Hom 入力を使って同定する。
方針：入力 fiber の外延性で native 端点を求め、Hom 模型同型の逆で移す。
規約：対角だけの一致や端点だけの入力一致で代用しない。
使われ方：正本入力 lift と単位補正道を同じ三辺境界に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

lemma dgGluingNativePreCollarInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstCompositionInputLift R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily_one R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_input R C D M X Y,
      ← Category.assoc, ι₁_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstCompositionInputLift_input R C D M X Y]

lemma dgGluingNativeExitCollarInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastCompositionInputLift R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily_zero R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_input R C D M X Y,
      ← Category.assoc, ι₀_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastCompositionInputLift_input R C D M X Y]

lemma dgGluingNativePreCapInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath R C D M X Y =
      ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreUnitCapTriangleFamily_zero R C D M X Y]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_input R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_input R C D M X Y]

lemma dgGluingNativeExitCapInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath R C D M X Y =
      ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCapTriangleFamily_one R C D M X Y]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_input R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_input R C D M X Y]

lemma dgGluingPreCollarModelInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomFirstCompositionInputLift R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath, ← Category.assoc, ι₁_comp,
    Category.assoc, dgGluingNativePreCollarInputPath_one R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma dgGluingExitCollarModelInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLaxHomLastCompositionInputLift R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath, ← Category.assoc, ι₀_comp,
    Category.assoc, dgGluingNativeExitCollarInputPath_zero R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma dgGluingPreCapModelInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCapModelInputPath R C D M X Y =
      ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath R C D M X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCapModelInputPath, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath,
    ι₀_comp_assoc]
  rw [dgGluingNativePreCapInputPath_zero R C D M X Y]

lemma dgGluingExitCapModelInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCapModelInputPath R C D M X Y =
      ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath R C D M X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCapModelInputPath, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath,
    ι₁_comp_assoc]
  rw [dgGluingNativeExitCapInputPath_one R C D M X Y]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
