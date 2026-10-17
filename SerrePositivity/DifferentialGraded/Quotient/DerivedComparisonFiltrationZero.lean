module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltration

/-! # 長さ filtration の零段と元の Hom の同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 内部 path 直和から空 path だけを取り出す chain map。 -/
def internalEmptyProjection (S : Set D) (x y : D) :
    internalHom A D S x y ⟶ homObject A D x y :=
  Sigma.desc (fun w : Word S => match w with
    | [] => 𝟙 _
    | _ :: _ => 0)

lemma originalHom_emptyProjection (S : Set D) (x y : D) :
    originalHom A D S x y ≫ internalEmptyProjection A D S x y = 𝟙 _ :=
  Sigma.ι_comp_desc _ _

lemma originalHom_f_injective (S : Set D) (x y : D) (i : ℤ) :
    Function.Injective ((originalHom A D S x y).f i) := by
  apply Function.LeftInverse.injective (g := (internalEmptyProjection A D S x y).f i)
  intro z
  have h := congrArg (fun f : homObject A D x y ⟶ homObject A D x y => f.f i z)
    (originalHom_emptyProjection A D S x y)
  simpa only [HomologicalComplex.comp_f, ModuleCat.comp_apply, HomologicalComplex.id_f,
    ModuleCat.id_apply] using h

/-- 零段の各次数は、元の Hom の次数ごとの像に等しい。 -/
lemma lengthSubmodule_zero (S : Set D) (x y : D) (i : ℤ) :
    lengthSubmodule A D S x y 0 i = LinearMap.range ((originalHom A D S x y).f i).hom := by
  apply le_antisymm
  · refine iSup_le (fun w => iSup_le (fun hw => ?_))
    have hw' : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    exact le_rfl
  · rintro z ⟨t, rfl⟩
    exact path_mem_lengthSubmodule A D S x y 0 i [] le_rfl t

def lengthZeroLinearMap (S : Set D) (x y : D) (i : ℤ) :
    (homObject A D x y).X i →ₗ[A] lengthSubmodule A D S x y 0 i :=
  LinearMap.codRestrict _ ((originalHom A D S x y).f i).hom
    (fun z => path_mem_lengthSubmodule A D S x y 0 i [] le_rfl z)

lemma lengthZeroLinearMap_coe (S : Set D) (x y : D) (i : ℤ)
    (z : (homObject A D x y).X i) :
    (lengthZeroLinearMap A D S x y i z).val = (originalHom A D S x y).f i z := rfl

lemma lengthZeroLinearMap_bijective (S : Set D) (x y : D) (i : ℤ) :
    Function.Bijective (lengthZeroLinearMap A D S x y i) := by
  constructor
  · intro z t h
    exact originalHom_f_injective A D S x y i (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    rw [lengthSubmodule_zero] at hz
    obtain ⟨t, ht⟩ := hz
    exact ⟨t, Subtype.ext ht⟩

lemma lengthZeroLinearMap_d (S : Set D) (x y : D) (i : ℤ) :
    (lengthDifferential A D S x y 0 i).comp (lengthZeroLinearMap A D S x y i) =
      (lengthZeroLinearMap A D S x y (i + 1)).comp ((homObject A D x y).d i (i + 1)).hom := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  simp only [LinearMap.comp_apply, lengthDifferential_coe, lengthZeroLinearMap_coe]
  have h := congrArg
    (fun f : (homObject A D x y).X i ⟶ (quotientHom A D S x y).X (i + 1) => f z)
    ((originalHomInclusion A D S x y).comm i (i + 1))
  simp only [ModuleCat.comp_apply, originalHomInclusion_f] at h
  convert h using 1

/-- 元の Hom を最終微分の零段へ入れる chain map。 -/
def lengthZeroMap (S : Set D) (x y : D) : homObject A D x y ⟶ lengthComplex A D S x y 0 :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (lengthZeroLinearMap A D S x y i))
    (fun i => by
      rw [lengthComplex_d]
      exact ModuleCat.hom_ext (lengthZeroLinearMap_d A D S x y i))

instance lengthZeroMap_isIso (S : Set D) (x y : D) : IsIso (lengthZeroMap A D S x y) := by
  have (i : ℤ) : IsIso ((lengthZeroMap A D S x y).f i) :=
    (LinearEquiv.toModuleIso (LinearEquiv.ofBijective (lengthZeroLinearMap A D S x y i)
      (lengthZeroLinearMap_bijective A D S x y i))).isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 零段は元の Hom 複体そのものである。 -/
def lengthZeroIso (S : Set D) (x y : D) : homObject A D x y ≅ lengthComplex A D S x y 0 :=
  asIso (lengthZeroMap A D S x y)

@[reassoc] lemma lengthZeroMap_inclusion (S : Set D) (x y : D) :
    lengthZeroMap A D S x y ≫ lengthInclusion A D S x y 0 = originalHomInclusion A D S x y := by
  ext i z
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
