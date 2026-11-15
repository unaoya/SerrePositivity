module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.Components
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# 係数制限と同じ指定積全複体

## 概要
S 上の指定積全複体を係数制限した複体と、各行を制限して取る R 上の指定全複体を比較する。

## 方針
元の行射影を係数制限して積へ持ち上げ、同じ成分表示で同型性を確認する。

## 規約
新しい S 作用は構成しない。与えられた S 線形図式の作用を保つ。

## 使われ方
BS 著者版 Lemma 4.22 の標準 S 線形比較の制限後の成分照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 係数制限を各内部複体へ施した元の横図式。 -/
abbrev restrictedRows (f : R →+* S) (K : CochainComplex (Complex S) ℕ) :
    CochainComplex (Complex R) ℕ :=
  ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
    (.up ℕ)).obj K)

/-- 元の S 行射影から、同じ指定 R 積へ取る持ち上げ。 -/
def restrictionTotalDegree (f : R →+* S) (K : CochainComplex (Complex S) ℕ) (q : ℤ) :
    (ModuleCat.restrictScalars f).obj ((total K).X q) ⟶ (total (restrictedRows f K)).X q :=
  componentLift (restrictedRows f K) q (fun n => (ModuleCat.restrictScalars f).map (componentπ K n q))

/-- 比較後の指定成分は、元の指定成分の係数制限である。 -/
@[reassoc] theorem restrictionTotalDegree_π
    (f : R →+* S) (K : CochainComplex (Complex S) ℕ) (q : ℤ) (n : ℕ) :
    restrictionTotalDegree f K q ≫ componentπ (restrictedRows f K) n q =
      (ModuleCat.restrictScalars f).map (componentπ K n q) :=
  componentLift_π (restrictedRows f K) q _ n

/-- 同じ成分比較は全微分と可換である。 -/
def restrictionTotalComparison (f : R →+* S) (K : CochainComplex (Complex S) ℕ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (total K) ⟶
      total (restrictedRows f K) where
  f q := restrictionTotalDegree f K q
  comm' i j hij := by
    change i+1=j at hij
    subst j
    apply component_hom_ext
    intro n
    change restrictionTotalDegree f K i ≫ (total (restrictedRows f K)).d i (i+1) ≫
        componentπ (restrictedRows f K) n (i+1) =
      (ModuleCat.restrictScalars f).map ((total K).d i (i+1)) ≫
        (restrictionTotalDegree f K (i+1) ≫ componentπ (restrictedRows f K) n (i+1))
    rw [restrictionTotalDegree_π]
    cases n with
    | zero =>
      rw [component_d_zero, ← Category.assoc, restrictionTotalDegree_π]
      change (ModuleCat.restrictScalars f).map (componentπ K 0 i) ≫
          (ModuleCat.restrictScalars f).map ((K.X 0).d (i-0) (i+1-0)) = _
      rw [← Functor.map_comp, ← Functor.map_comp, component_d_zero]
    | succ n =>
      rw [component_d_succ, Preadditive.comp_add, Linear.comp_units_smul]
      simp only [← Category.assoc, restrictionTotalDegree_π]
      have h := congrArg (ModuleCat.restrictScalars f).map (component_d_succ K n i)
      simpa only [Functor.map_add, Functor.map_comp, Units.smul_def, Functor.map_zsmul,
        eqToHom_map, restrictedRows, Functor.mapHomologicalComplex_obj_X,
        Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f,
        Category.assoc] using h.symm

/-- 同じ指定成分を保つ比較は各次数で全単射である。 -/
theorem restrictionTotalDegree_isIso (f : R →+* S) (K : CochainComplex (Complex S) ℕ) (q : ℤ) :
    IsIso (restrictionTotalDegree f K q) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply (componentsLinearEquiv K q).injective
    funext n
    have h := congrArg (fun z => componentπ (restrictedRows f K) n q z) hxy
    simp only [← ModuleCat.comp_apply, restrictionTotalDegree_π,
      ModuleCat.restrictScalars.map_apply] at h
    exact h
  · intro y
    let x := (componentsLinearEquiv K q).symm (fun n => componentπ (restrictedRows f K) n q y)
    refine ⟨x, ?_⟩
    apply ext
    intro n
    rw [← ModuleCat.comp_apply, restrictionTotalDegree_π]
    exact congrArg (fun v => v n) ((componentsLinearEquiv K q).apply_symm_apply
      (fun n => componentπ (restrictedRows f K) n q y))

/-- 係数制限と指定積全複体の元の成分を保つ鎖同型。 -/
def restrictionTotalIso (f : R →+* S) (K : CochainComplex (Complex S) ℕ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj (total K) ≅
      total (restrictedRows f K) := by
  haveI : ∀ q : ℤ, IsIso ((restrictionTotalComparison f K).f q) :=
    fun q => restrictionTotalDegree_isIso f K q
  haveI := HomologicalComplex.Hom.isIso_of_components (restrictionTotalComparison f K)
  exact asIso (restrictionTotalComparison f K)


/-- 同じ指定成分を保つ係数制限の比較は、S 線形の図式の射について自然である。 -/
@[reassoc] theorem restrictionTotalComparison_naturality (f : R →+* S)
    {K M : CochainComplex (Complex S) ℕ} (g : K ⟶ M) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        ((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map g) ≫
      restrictionTotalComparison f M = restrictionTotalComparison f K ≫
        (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
          ((((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).mapHomologicalComplex
            (.up ℕ)).map g) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply component_hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, restrictionTotalComparison, Category.assoc,
    restrictionTotalDegree_π, componentπ_naturality, restrictionTotalDegree_π_assoc]
  change (ModuleCat.restrictScalars f).map
      (((cochainProductTotalizationFunctor (ModuleCat.{u} S)).map g).f q) ≫
        (ModuleCat.restrictScalars f).map (componentπ M n q) =
      (ModuleCat.restrictScalars f).map (componentπ K n q) ≫
        (ModuleCat.restrictScalars f).map ((g.f n).f (q-n))
  rw [← Functor.map_comp, ← Functor.map_comp, componentπ_naturality]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
