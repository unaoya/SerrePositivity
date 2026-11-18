module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Normalization.NatComplex

/-!
# 同じ正規化核の写像と自然な包含

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L20、報告 §397。
元の余単体的写像を各核へ制限し、同じ包含の自然性を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory _root_.AlgebraicTopology
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元の余単体的写像は全codegeneracy核を保つ（Dold–Kan、BF §2.2）。 -/
lemma normalized_map_mem {X Y : CosimplicialObject (ModuleCat.{u} A)}
    (f : X ⟶ Y) (q : ℕ) (a : _root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X q) :
    (f.app ⦋q⦌) a.val ∈ _root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A Y q := by
  cases q with
  | zero => exact Submodule.mem_top
  | succ q =>
    apply (_root_.SerrePositivity.CosimplicialNormalization.mem_normalized_succ A Y q _).mpr
    intro i
    have H := ConcreteCategory.congr_hom (f.naturality (SimplexCategory.σ i)) a.val
    change (f.app ⦋q⦌) ((X.σ i) a.val) = (Y.σ i) ((f.app ⦋q + 1⦌) a.val) at H
    rw [(_root_.SerrePositivity.CosimplicialNormalization.mem_normalized_succ A X q a.val).mp a.property i, map_zero] at H
    exact H.symm

/-- 元の写像の各核への制限による正規化複体の射（Dold–Kan、BF §2.2）。 -/
def normalizedMapNat {X Y : CosimplicialObject (ModuleCat.{u} A)} (f : X ⟶ Y) :
    _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A X ⟶ _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A Y :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom
    { toFun a := ⟨(f.app ⦋q⦌) a.val, _root_.SerrePositivity.CosimplicialNormalization.normalized_map_mem A f q a⟩
      map_add' a b := by apply Subtype.ext; exact map_add _ _ _
      map_smul' r a := by apply Subtype.ext; exact map_smul _ _ _ }) (fun q => by
    dsimp only [_root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    have H := ConcreteCategory.congr_hom ((AlternatingCofaceMapComplex.map f).comm q (q + 1)) a.val
    dsimp only [AlternatingCofaceMapComplex.map, AlternatingCofaceMapComplex.obj] at H
    rw [CochainComplex.of_d, CochainComplex.of_d] at H
    change (AlternatingCofaceMapComplex.objD Y q) ((f.app ⦋q⦌) a.val) =
      (f.app ⦋q + 1⦌) ((AlternatingCofaceMapComplex.objD X q) a.val) at H
    change _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A Y q ((f.app ⦋q⦌) a.val) =
      (f.app ⦋q + 1⦌) (_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces A X q a.val)
    rw [_root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom, _root_.SerrePositivity.CosimplicialNormalization.alternatingCofaces_eq_objD_hom]
    exact H)

/-- 元の全余単体的加群の正規化複体関手（Dold–Kan、BF §2.2）。 -/
def normalizedCochainNatFunctor :
    CosimplicialObject (ModuleCat.{u} A) ⥤ CochainComplex (ModuleCat.{u} A) ℕ where
  obj := _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNat A
  map := _root_.SerrePositivity.CosimplicialNormalization.normalizedMapNat A
  map_id X := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

/-- 同じ元の部分加群の包含の全自然変換（Dold–Kan、BF §2.2）。 -/
def normalizationInclusionNat :
    _root_.SerrePositivity.CosimplicialNormalization.normalizedCochainNatFunctor A ⟶ alternatingCofaceMapComplex (ModuleCat A) where
  app := _root_.SerrePositivity.CosimplicialNormalization.normInclusionNat A
  naturality := by
    intro X Y f
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl

end SerrePositivity.CosimplicialNormalization
