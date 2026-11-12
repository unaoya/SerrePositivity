module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitInputModelPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionInputTriangleExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeCanonicalUnitCapEndpoints
/-! # 元入力付き単位補正道の正本係数端

概要：二補正道の正本係数端を、三角形全体と元 Hom 入力を使って同定する。
方針：正本係数三角形の全体評価から native 端点を求め、Hom 模型同型の逆で移す。
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


lemma dgGluingNativePreCapInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreUnitCapTriangleFamily_one_canonical R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_input R C D M X Y,
      ← Category.assoc, ι₁_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift_input R C D M X Y]

lemma dgGluingPreCapModelInputPath_one :
    ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCapModelInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedFirstCompositionInputLift R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCapModelInputPath, ← Category.assoc, ι₁_comp,
    Category.assoc, dgGluingNativePreCapInputPath_one R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

lemma dgGluingNativeExitCapInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift R C D M X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangle_hom_ext R C D M X Y
  · simp only [whiskerLeft_comp, Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_evaluation R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCapTriangleFamily_zero_canonical R C D M X Y,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_triangle R C D M X Y]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_input R C D M X Y,
      ← Category.assoc, ι₀_fst, Category.id_comp, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift_input R C D M X Y]

lemma dgGluingExitCapModelInputPath_zero :
    ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCapModelInputPath R C D M X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLastCompositionInputLift R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCapModelInputPath, ← Category.assoc, ι₀_comp,
    Category.assoc, dgGluingNativeExitCapInputPath_zero R C D M X Y,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso_hom R C D M X Y, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
