module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDiskCoverAcyclic
/-!
概要：元の任意の加群射を同じ disk 被覆の二つの実射から回収する。
方針：実直和の第一射影と、元の射・被覆射の和を作る。
規約：元の射を同じ第一包含後の右射として保持する。使われ方：非全射準同型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の始域と終域の実 disk 被覆との同じ直和。 -/
def dgModuleQuasiIsoSpanObject (M N : ModuleCategory R D) : ModuleCategory R D :=
  moduleBiprod R D M (moduleDiskCover R D N)
/-- 同じ実直和から元の始域への第一射影。 -/
def dgModuleQuasiIsoSpanLeft (M N : ModuleCategory R D) :
    dgModuleQuasiIsoSpanObject R D M N ⟶ M :=
  moduleBiprodFst R D M (moduleDiskCover R D N)
/-- 同じ実直和から元の終域への、指定射と実被覆射の和。 -/
def dgModuleQuasiIsoSpanRight {M N : ModuleCategory R D} (f : M ⟶ N) :
    dgModuleQuasiIsoSpanObject R D M N ⟶ N :=
  moduleBiprodFst R D M (moduleDiskCover R D N) ≫ f +
    moduleBiprodSnd R D M (moduleDiskCover R D N) ≫ moduleDiskCoverπ R D N
/-- 同じ第一包含に沿い、右射から元の指定射を厳密に回収する。 -/
lemma dgModuleQuasiIsoSpan_inl_right {M N : ModuleCategory R D} (f : M ⟶ N) :
    moduleBiprodInl R D M (moduleDiskCover R D N) ≫ dgModuleQuasiIsoSpanRight R D f = f := by
  change (moduleBinaryBicone R D M (moduleDiskCover R D N)).inl ≫
    ((moduleBinaryBicone R D M (moduleDiskCover R D N)).fst ≫ f +
      (moduleBinaryBicone R D M (moduleDiskCover R D N)).snd ≫ moduleDiskCoverπ R D N) = f
  rw [Preadditive.comp_add, ← Category.assoc, BinaryBicone.inl_fst, Category.id_comp,
    ← Category.assoc, BinaryBicone.inl_snd, zero_comp, add_zero]
/-- 同じ第二包含に沿い、右射から元の実 disk 被覆射を回収する。 -/
lemma dgModuleQuasiIsoSpan_inr_right {M N : ModuleCategory R D} (f : M ⟶ N) :
    moduleBiprodInr R D M (moduleDiskCover R D N) ≫ dgModuleQuasiIsoSpanRight R D f =
      moduleDiskCoverπ R D N := by
  change (moduleBinaryBicone R D M (moduleDiskCover R D N)).inr ≫
    ((moduleBinaryBicone R D M (moduleDiskCover R D N)).fst ≫ f +
      (moduleBinaryBicone R D M (moduleDiskCover R D N)).snd ≫ moduleDiskCoverπ R D N) = _
  rw [Preadditive.comp_add, ← Category.assoc, BinaryBicone.inr_fst, zero_comp,
    ← Category.assoc, BinaryBicone.inr_snd, Category.id_comp, zero_add]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
