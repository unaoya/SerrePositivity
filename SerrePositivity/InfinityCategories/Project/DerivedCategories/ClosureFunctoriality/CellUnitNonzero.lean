module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellDegreeSplitting
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
概要：標準 cell 分解は、係数環が非零なら全対象で非零の厳密単位を持つ。
方針：段零の空 path から単位複体への射影を、次数別分裂に合成する。
規約：単位が境界となる場合もある。ホモロジーでの非零性は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits MonoidalCategory DifferentialGraded HomologicalComplex
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 初期自由圏の空 path だけを読む射影。 -/
def dgCellInitialUnitProjection (x : D) :
    stageHom R D 0 x x ⟶ 𝟙_ (Complex R) :=
  Sigma.desc (fun p => match p with
    | .inl _ => 𝟙 _
    | .inr _ => 0)

lemma dgCellInitialUnitProjection_split (x : D) :
    (stage R D 0).category.id x ≫ dgCellInitialUnitProjection R D x = 𝟙 _ :=
  Sigma.ι_desc _ _

/-- 最終分解の次数零から空 path の係数を読む加群射。 -/
def dgCellUnitCoefficient (x : D) :
    (candidateHom R D x x).X 0 ⟶ (𝟙_ (Complex R)).X 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellStageZeroRetraction R D x x 0 ≫ (dgCellInitialUnitProjection R D x).f 0

lemma dgCellUnitCoefficient_split (x : D) :
    (candidateUnit R D x).f 0 ≫ dgCellUnitCoefficient R D x = 𝟙 _ := by
  rw [candidateUnit, HomologicalComplex.comp_f, dgCellUnitCoefficient]
  calc
    _ = ((stage R D 0).category.id x).f 0 ≫
        ((stageInclusion R D 0 x x).f 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellStageZeroRetraction R D x x 0) ≫
          (dgCellInitialUnitProjection R D x).f 0 := by simp only [Category.assoc]
    _ = 𝟙 _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellStageZeroRetraction_split, Category.id_comp]
      exact congrArg (fun f => f.f 0) (dgCellInitialUnitProjection_split R D x)

/-- cell 分解の単位の係数を、係数環の元として読む。 -/
def dgCellUnitScalar (x : Source R D) :
    (homObject R (Source R D) x x).X 0 →ₗ[R] R :=
  (dgCellUnitCoefficient R D x.val ≫
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).hom).hom

lemma dgCellUnitScalar_unit (x : Source R D) :
    dgCellUnitScalar R D x (unitElement R x).val = 1 := by
  let s := (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R)
  have h := ConcreteCategory.congr_hom (dgCellUnitCoefficient_split R D x.val) s
  change dgCellUnitCoefficient R D x.val ((unitElement R x).val) = s at h
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).hom
    (dgCellUnitCoefficient R D x.val ((unitElement R x).val)) = 1
  rw [h]
  exact ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv_hom_id
    (1 : R)

/-- 分解の各対象の単位は、鎖の元として非零である。 -/
lemma dgCellResolution_unit_ne_zero [Nontrivial R] (x : Source R D) :
    (unitElement R x).val ≠ 0 := by
  intro hz
  let s := (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R)
  have h := congrArg (fun f => f s) (dgCellUnitCoefficient_split R D x.val)
  change dgCellUnitCoefficient R D x.val ((unitElement R x).val) = s at h
  rw [hz, map_zero] at h
  have he := congrArg (fun z => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).hom z) h
  have ho : (0 : R) = 1 := by simpa [s] using he
  exact zero_ne_one ho

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
