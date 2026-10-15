module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced

/-! # balanced tensorの両変数の作用可換なchain map族 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M M' : RightModule A D} {N N' : LeftModule A D}

/-- 対象の直和上の両変数map。 -/
def generatorMap (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x, N.obj x ⟶ N'.obj x) : generators A D M N ⟶ generators A D M' N' :=
  Limits.Sigma.map (fun x : D => f x ⊗ₘ g x)

/-- 関係の直和上の両変数map。 -/
def relationMap (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (g : ∀ x, N.obj x ⟶ N'.obj x) : relations A D M N ⟶ relations A D M' N' :=
  Limits.Sigma.map (fun xy : D × D => (f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1)

lemma relationLeft_naturality
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A D M' x y) :
    relationMap A D f g ≫ relationLeft A D M' N' =
      relationLeft A D M N ≫ generatorMap A D f g := by
  apply Sigma.hom_ext
  intro xy
  simp only [relationMap, relationLeft, generatorMap, Sigma.ι_map_assoc,
    Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_map]
  have h : ((f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1) ≫
      (rightAction A D M' xy.1 xy.2 ⊗ₘ 𝟙 (N'.obj xy.1)) =
    (rightAction A D M xy.1 xy.2 ⊗ₘ 𝟙 (N.obj xy.1)) ≫ (f xy.1 ⊗ₘ g xy.1) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [hf]
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun h => h ≫ Sigma.ι (objectFamily A D M' N') xy.1) h

lemma relationRight_naturality
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, leftAction A D N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A D N' x y) :
    relationMap A D f g ≫ relationRight A D M' N' =
      relationRight A D M N ≫ generatorMap A D f g := by
  apply Sigma.hom_ext
  intro xy
  simp only [relationMap, relationRight, generatorMap, Sigma.ι_map_assoc,
    Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Category.assoc, Sigma.ι_map]
  have h : ((f xy.2 ⊗ₘ 𝟙 (xy.1 ⟶[Complex A] xy.2)) ⊗ₘ g xy.1) ≫
      (α_ (M'.obj (op xy.2)) (xy.1 ⟶[Complex A] xy.2) (N'.obj xy.1)).hom ≫
        (𝟙 (M'.obj (op xy.2)) ⊗ₘ leftAction A D N' xy.1 xy.2) =
    (α_ (M.obj (op xy.2)) (xy.1 ⟶[Complex A] xy.2) (N.obj xy.1)).hom ≫
      (𝟙 (M.obj (op xy.2)) ⊗ₘ leftAction A D N xy.1 xy.2) ≫ (f xy.2 ⊗ₘ g xy.2) := by
    rw [associator_naturality_assoc]
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    rw [hg]
  simpa only [id_tensorHom, Category.assoc] using
    congrArg (fun h => h ≫ Sigma.ι (objectFamily A D M' N') xy.2) h

/-- 作用と可換な両変数のchain map族をbalanced tensorへ降ろす。 -/
def mapOfFamilies
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A D M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A D M' x y)
    (hg : ∀ x y, leftAction A D N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A D N' x y) :
    obj A D M N ⟶ obj A D M' N' :=
  coequalizer.desc (generatorMap A D f g ≫ projection A D M' N') (by
    rw [← Category.assoc, ← relationLeft_naturality A D f g hf, Category.assoc,
      projection, coequalizer.condition, ← Category.assoc,
      relationRight_naturality A D f g hg, Category.assoc])

@[reassoc (attr := simp)]
lemma ι_mapOfFamilies
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x) (hf hg) (x : D) :
    ι A D M N x ≫ mapOfFamilies A D f g hf hg = (f x ⊗ₘ g x) ≫ ι A D M' N' x := by
  simp only [ι, mapOfFamilies, projection, Category.assoc, coequalizer.π_desc,
    generatorMap, Sigma.ι_map_assoc]

lemma mapOfFamilies_id (M : RightModule A D) (N : LeftModule A D) (hf hg) :
    mapOfFamilies A D (fun x => 𝟙 (M.obj (op x))) (fun x => 𝟙 (N.obj x)) hf hg =
      𝟙 (obj A D M N) := by
  apply hom_ext
  intro x
  simp

variable {M'' : RightModule A D} {N'' : LeftModule A D}
lemma mapOfFamilies_comp
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (f' : ∀ x, M'.obj (op x) ⟶ M''.obj (op x)) (g' : ∀ x, N'.obj x ⟶ N''.obj x)
    (hf hg hf' hg' hff hgg) :
    mapOfFamilies A D f g hf hg ≫ mapOfFamilies A D f' g' hf' hg' =
      mapOfFamilies A D (fun x => f x ≫ f' x) (fun x => g x ≫ g' x) hff hgg := by
  apply hom_ext
  intro x
  rw [ι_mapOfFamilies_assoc, ι_mapOfFamilies, ι_mapOfFamilies]
  simp only [tensorHom_comp_tensorHom_assoc]

end SerrePositivity.DifferentialGraded.BalancedTensor
