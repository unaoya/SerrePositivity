module

public import SerrePositivity.AlgebraicGeometry.CechZeroTermExtension

/-!
概要：零次項に加えた中心の加群からの増大写像を差し引く、複体の実際の射。
方針：零次で二つの制限の差を取り、正次数では元の射を使う。
規約：中心の増大写像の像がコサイクルであることだけを構成に使う。
使われ方：F8 のブローアップ四角形の差の余鎖写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (C D : CochainComplex (ModuleCat.{u} R) ℕ) (f : C ⟶ D)
variable (Q : ModuleCat.{u} R) (γ : Q →ₗ[R] D.X 0)

/-- 零次では二つの制限の差、正次数では元の射の成分。 -/
def cechZeroTermDifferenceComponent :
    ∀ n, (cechZeroTermExtension C Q).X n ⟶ D.X n
  | 0 => { hom' := (f.f 0).hom.comp (LinearMap.fst R _ _) - γ.comp (LinearMap.snd R _ _) }
  | n + 1 => f.f (n + 1)

/-- 中心の増大写像を差し引いた複体の射。 -/
def cechZeroTermDifference
    (hγ : ∀ q, (D.d 0 1).hom (γ q) = 0) : cechZeroTermExtension C Q ⟶ D :=
  CochainComplex.ofHom (cechZeroTermDifferenceComponent C D f Q γ) (by
    intro n
    cases n with
    | zero =>
      change cechZeroTermDifferenceComponent C D f Q γ 0 ≫ D.d 0 1 =
        (cechZeroTermExtension C Q).d 0 1 ≫ f.f 1
      rw [cechZeroTermExtension_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (D.d 0 1).hom ((f.f 0).hom x.1 - γ x.2) =
        (f.f 1).hom ((C.d 0 1).hom x.1)
      rw [map_sub, hγ, sub_zero]
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
        congrArg (fun g ↦ g.hom x.1) (f.comm 0 1)
    | succ n =>
      change f.f (n + 1) ≫ D.d (n + 1) (n + 2) =
        (cechZeroTermExtension C Q).d (n + 1) (n + 2) ≫ f.f (n + 2)
      rw [cechZeroTermExtension_d]
      exact f.comm (n + 1) (n + 2))

private theorem shortComplexHomologyMap_eq_of_middle
    {S T : ShortComplex (ModuleCat.{u} R)} (φ ψ : S ⟶ T) (h : φ.τ₂ = ψ.τ₂) :
    ShortComplex.homologyMap φ = ShortComplex.homologyMap ψ := by
  apply (cancel_epi S.homologyπ).mp
  apply (cancel_mono T.homologyι).mp
  simp only [Category.assoc, ShortComplex.π_homologyMap_ι, h]

/-- 正次数では差の射は元の射と射影の合成と同じ H の射を誘導する。 -/
theorem cechZeroTermDifference_positive_homology
    (hγ : ∀ q, (D.d 0 1).hom (γ q) = 0) (n : ℕ) :
    ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map (cechZeroTermDifference C D f Q γ hγ)) =
    ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map (cechZeroTermProjection C Q ≫ f)) := by
  apply shortComplexHomologyMap_eq_of_middle
  change f.f (n + 1) = 𝟙 _ ≫ f.f (n + 1)
  rw [Category.id_comp]

/-- 元の射が正次数の H で同型なら、中心の項を足した差の射もそうなる。 -/
theorem cechZeroTermDifference_positive_homology_isIso
    (hγ : ∀ q, (D.d 0 1).hom (γ q) = 0)
    (hf : ∀ n, IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map f))) (n : ℕ) :
    IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map (cechZeroTermDifference C D f Q γ hγ))) := by
  rw [cechZeroTermDifference_positive_homology, Functor.map_comp,
    ShortComplex.homologyMap_comp]
  haveI := cechZeroTermProjection_positive_homology_isIso C Q n
  haveI := hf n
  infer_instance

end SerrePositivity.AlgebraicGeometry
