module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.Differential

/-!
# 同じ全codegeneracy核の制限微分と包含

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L20、報告 §397。
元の交代余面複体の二乗零を同じ部分加群で判定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 制限前の微分は元の交代余面複体の微分（Dold–Kan、BF §2.2）。 -/
lemma alternatingCofaces_eq_objD_hom (q : ℕ) :
    _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X q = (AlternatingCofaceMapComplex.objD X q).hom := by
  simp only [_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces, AlternatingCofaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]

/-- 同じ交代余面微分を元の正規化核へ制限する（Dold–Kan、BF §2.2）。 -/
def normalizedDifferential (q : ℕ) :
    ModuleCat.of A (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q) ⟶ ModuleCat.of A (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X (q + 1)) :=
  ModuleCat.ofHom
    { toFun a := ⟨_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X q a.val, _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_mem A X q a⟩
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _
      map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _ }

/-- 元の交代余面微分の二乗零を同じ部分加群で判定（Dold–Kan、BF §2.2）。 -/
lemma normalizedDifferential_squared (q : ℕ) :
    _root_.SerrePositivity.CosimplicialNormalization.normalizedDifferential A X q ≫ _root_.SerrePositivity.CosimplicialNormalization.normalizedDifferential A X (q + 1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X (q + 1) (_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X q a.val) = 0
  rw [_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom, _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom]
  exact ConcreteCategory.congr_hom (AlternatingCofaceMapComplex.d_squared X q) a.val

/-- 同じ正規化核の自然数コチェイン複体（Dold–Kan、BF §2.2）。 -/
def normalizedCochainNat : CochainComplex (ModuleCat.{u} A) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of A (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q))
    (_root_.SerrePositivity.CosimplicialNormalization.normalizedDifferential A X) (_root_.SerrePositivity.CosimplicialNormalization.normalizedDifferential_squared A X)

/-- 元の部分加群の包含を同じ交代余面複体の射に束ねる（Dold–Kan、BF §2.2）。 -/
def normInclusionNat :
    _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A X ⟶ (alternatingCofaceMapComplex (ModuleCat A)).obj X :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q).subtype) (fun q => by
    dsimp only [_root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat, alternatingCofaceMapComplex,
      AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact congrArg (fun l => l a.val) (_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom A X q).symm)

end SerrePositivity.CosimplicialNormalization
