module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitInputModelPaths
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputTriangleExt
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

lemma dgGluingNativePreCollarInputPath_one :
    ι₁ ≫ dgGluingNativePreCollarInputPath R C D M X Y =
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingLaxHomFirstCompositionInputLift R C D M X Y := by
  apply dgGluingDerivedFirstInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
      dgGluingNativePreNormalizeUnitCollarTriangleFamily_one R C D M X Y,
      dgGluingLaxHomFirstCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, dgGluingNativePreCollarInputPath_input R C D M X Y,
      ← Category.assoc, ι₁_fst, Category.id_comp, Category.assoc,
      dgGluingLaxHomFirstCompositionInputLift_input R C D M X Y]

lemma dgGluingNativeExitCollarInputPath_zero :
    ι₀ ≫ dgGluingNativeExitCollarInputPath R C D M X Y =
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingLaxHomLastCompositionInputLift R C D M X Y := by
  apply dgGluingDerivedLastInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
      dgGluingNativeExitUnitCollarTriangleFamily_zero R C D M X Y,
      dgGluingLaxHomLastCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, dgGluingNativeExitCollarInputPath_input R C D M X Y,
      ← Category.assoc, ι₀_fst, Category.id_comp, Category.assoc,
      dgGluingLaxHomLastCompositionInputLift_input R C D M X Y]

lemma dgGluingNativePreCapInputPath_zero :
    ι₀ ≫ dgGluingNativePreCapInputPath R C D M X Y =
      ι₀ ≫ dgGluingNativePreCollarInputPath R C D M X Y := by
  apply dgGluingDerivedFirstInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [dgGluingNativePreCapInputPath_evaluation R C D M X Y,
      dgGluingNativePreCollarInputPath_evaluation R C D M X Y,
      dgGluingNativePreUnitCapTriangleFamily_zero R C D M X Y]
  · simp only [Category.assoc, dgGluingNativePreCapInputPath_input R C D M X Y,
      dgGluingNativePreCollarInputPath_input R C D M X Y]

lemma dgGluingNativeExitCapInputPath_one :
    ι₁ ≫ dgGluingNativeExitCapInputPath R C D M X Y =
      ι₁ ≫ dgGluingNativeExitCollarInputPath R C D M X Y := by
  apply dgGluingDerivedLastInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [dgGluingNativeExitCapInputPath_evaluation R C D M X Y,
      dgGluingNativeExitCollarInputPath_evaluation R C D M X Y,
      dgGluingNativeExitUnitCapTriangleFamily_one R C D M X Y]
  · simp only [Category.assoc, dgGluingNativeExitCapInputPath_input R C D M X Y,
      dgGluingNativeExitCollarInputPath_input R C D M X Y]

lemma dgGluingPreCollarModelInputPath_one :
    ι₁ ≫ dgGluingPreCollarModelInputPath R C D M X Y =
      dgGluingLaxHomFirstCompositionInputLift R C D M X Y := by
  rw [dgGluingPreCollarModelInputPath, ← Category.assoc, ι₁_comp,
    Category.assoc, dgGluingNativePreCollarInputPath_one R C D M X Y,
    ← dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma dgGluingExitCollarModelInputPath_zero :
    ι₀ ≫ dgGluingExitCollarModelInputPath R C D M X Y =
      dgGluingLaxHomLastCompositionInputLift R C D M X Y := by
  rw [dgGluingExitCollarModelInputPath, ← Category.assoc, ι₀_comp,
    Category.assoc, dgGluingNativeExitCollarInputPath_zero R C D M X Y,
    ← dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma dgGluingPreCapModelInputPath_zero :
    ι₀ ≫ dgGluingPreCapModelInputPath R C D M X Y =
      ι₀ ≫ dgGluingPreCollarModelInputPath R C D M X Y := by
  simp only [dgGluingPreCapModelInputPath, dgGluingPreCollarModelInputPath,
    ι₀_comp_assoc]
  rw [dgGluingNativePreCapInputPath_zero R C D M X Y]

lemma dgGluingExitCapModelInputPath_one :
    ι₁ ≫ dgGluingExitCapModelInputPath R C D M X Y =
      ι₁ ≫ dgGluingExitCollarModelInputPath R C D M X Y := by
  simp only [dgGluingExitCapModelInputPath, dgGluingExitCollarModelInputPath,
    ι₁_comp_assoc]
  rw [dgGluingNativeExitCapInputPath_one R C D M X Y]
end SerrePositivity.InfinityCategories
