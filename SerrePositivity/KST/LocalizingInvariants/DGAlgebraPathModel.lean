module

public import SerrePositivity.KST.LocalizingInvariants.DGEndAlgebra
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaProjections
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.ComplexMappingCoconeSndQuasiIso

/-!
概要：非可換 dg 代数の実経路代数と、両端への実代数射を構成する。
方針：恒等比較射を持つ D の実 comma dg 圏の自己準同型を用いる。
規約：独自の dg 合成則を仮定しない。使われ方：分解上の導来写像と経路の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

abbrev identityFunctor : DGFunctor R (DGAlgebraPoint R B) (DGAlgebraPoint R B) :=
  EnrichedFunctor.id (Complex R) (DGAlgebraPoint R B)

abbrev ArrowCategory :=
  DGFunctorCommaObject R (DGAlgebraPoint R B) (DGAlgebraPoint R B) (identityFunctor R B)

def identityPoint : ArrowCategory R B where
  source := .star
  replacement := .star
  augmentation := 𝟙 _

def algebra : Mon (Complex R) := dgEndAlgebra R (ArrowCategory R B) (identityPoint R B)

def source : algebra R B ⟶ B :=
  Mon.Hom.mk' (dgFunctorCommaSourceHomMap R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B))
    (dgFunctorCommaIdentity_source R _ _ _ (identityPoint R B))
    (dgFunctorCommaComposition_source R _ _ _ _ _ _)

def target : algebra R B ⟶ B :=
  Mon.Hom.mk' (dgFunctorCommaReplacementHomMap R _ _ (identityFunctor R B)
    (identityPoint R B) (identityPoint R B))
    (dgFunctorCommaIdentity_replacement R _ _ _ (identityPoint R B))
    (dgFunctorCommaComposition_replacement R _ _ _ _ _ _)

def difference : B.X ⊞ B.X ⟶ B.X :=
  dgFunctorCommaDifference R _ _ (identityFunctor R B) (identityPoint R B) (identityPoint R B)

lemma difference_eq : difference R B = biprod.fst - biprod.snd := by
  simp only [difference, dgFunctorCommaDifference, identityPoint, identityFunctor,
    EnrichedFunctor.id_map, eHomWhiskerRight_id, eHomWhiskerLeft_id]
  change ((biprod.fst : B.X ⊞ B.X ⟶ B.X) ≫ 𝟙 B.X ≫ 𝟙 B.X) -
    (biprod.snd : B.X ⊞ B.X ⟶ B.X) =
      (biprod.fst : B.X ⊞ B.X ⟶ B.X) - (biprod.snd : B.X ⊞ B.X ⟶ B.X)
  rw [Category.comp_id, Category.comp_id]

lemma source_quasiIso : QuasiIso (source R B).hom := by
  apply complexMappingCoconeProjection_quasiIso_of_eq (difference R B) (𝟙 B.X) (-(𝟙 B.X))
  · rw [difference_eq, biprod.desc_eq]
    simp only [Category.comp_id, Preadditive.comp_neg, sub_eq_add_neg]
  · exact quasiIso_of_isIso (-Iso.refl B.X).hom

lemma target_quasiIso : QuasiIso (target R B).hom := by
  apply complexMappingCoconeProjectionSnd_quasiIso_of_eq (difference R B) (𝟙 B.X) (-(𝟙 B.X))
  · rw [difference_eq, biprod.desc_eq]
    simp only [Category.comp_id, Preadditive.comp_neg, sub_eq_add_neg]
  · exact quasiIso_of_isIso _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
