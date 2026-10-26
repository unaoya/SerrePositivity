module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCommaFunctor
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImagePrism
/-!
概要：元終域の Hom gluing を同じ E の恒等 comma へ全 dg 関手として送る。
方針：元 comma 比較と既存の恒等 comma への像関手を合成する。
規約：元対象・全 Hom・第三 cochain・全 augmentation prism を保持する。
使われ方：元終域の二つの正規化 cube の実入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetIdentityCommaObject
    (X : DGGluingObject R C D M) : DGFunctorCommaObject R E E (DGFunctor.id E) :=
  dgGluingCommaImageObject R D E q (dgGluingHomTargetCommaObject R C D E p q X)

def dgGluingHomTargetIdentityCommaFunctor :
    DGFunctor R (DGGluingObject R C D M) (DGFunctorCommaObject R E E (DGFunctor.id E)) :=
  (dgGluingHomTargetToComma R C D E p q).comp (dgGluingCommaImageFunctor R D E q)

variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

lemma dgGluingHomTargetIdentityCommaFunctor_normalized :
    (dgGluingHomTargetIdentityCommaFunctor R C D E p q).map X Y ≫
      dgGluingIdentityCommaNormalizeHom R E
        (dgGluingHomTargetIdentityCommaObject R C D E p q X)
        (dgGluingHomTargetIdentityCommaObject R C D E p q Y) =
    dgGluingHomTargetNormalizedHom R C D E p q X Y := by
  change (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgGluingCommaImageHomMap R D E q
      (dgGluingHomTargetCommaObject R C D E p q X)
      (dgGluingHomTargetCommaObject R C D E p q Y)) ≫ _ = _
  rw [Category.assoc]
  rfl

/-- 恒等 comma に移した後の全 augmentation prism は元の同じ prism。 -/
lemma dgGluingHomTargetIdentityCommaFunctor_prism {n : ℕ}
    (s : Simplex R (DGGluingObject R C D M) n) (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
      (s.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q)) β =
    dgCommaAugmentationPrismSimplex R D E q
      (s.map (dgGluingHomTargetToComma R C D E p q)) β := by
  have hs : s.map (dgGluingHomTargetIdentityCommaFunctor R C D E p q) =
      (s.map (dgGluingHomTargetToComma R C D E p q)).map
        (dgGluingCommaImageFunctor R D E q) := by
    apply Simplex.ext
    exact SimplexData.map_comp _ _ _
  rw [hs]
  exact dgGluingCommaImagePrismSimplex R D E q _ β

end SerrePositivity.InfinityCategories
