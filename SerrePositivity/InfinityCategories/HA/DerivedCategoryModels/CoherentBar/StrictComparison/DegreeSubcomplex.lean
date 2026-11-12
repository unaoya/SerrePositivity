module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDegreeDifferential

/-!
概要：微分で保たれる次数部分加群を実複体として構成する。
方針：隣接微分を部分加群へ制限し、二乗零は元の複体で判定する。
規約：非有界の整数次数を使う。スペクトル系列の収束は仮定しない。
使われ方：coherent 正規化 bar の単体次元による実部分複体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (K : Complex R)
  (S : ∀ q : ℤ, Submodule R (K.X q))
  (hS : ∀ (q : ℤ) (z : K.X q), z ∈ S q → K.d q (q + 1) z ∈ S (q + 1))

def dgBarDegreeSubcomplexDifferential (q : ℤ) :
    ModuleCat.of R (S q) ⟶ ModuleCat.of R (S (q + 1)) :=
  ModuleCat.ofHom
    { toFun z := ⟨K.d q (q + 1) z.val, hS q z.val z.property⟩
      map_add' z w := by apply Subtype.ext; exact map_add _ _ _
      map_smul' r z := by apply Subtype.ext; exact map_smul _ _ _ }

lemma dgBarDegreeSubcomplexDifferential_squared (q : ℤ) :
    dgBarDegreeSubcomplexDifferential R K S hS q ≫
      dgBarDegreeSubcomplexDifferential R K S hS (q + 1) = 0 := by
  ext z
  exact ConcreteCategory.congr_hom (K.d_comp_d q (q + 1) (q + 1 + 1)) z.val

def dgBarDegreeSubcomplex : Complex R :=
  CochainComplex.of (fun q => ModuleCat.of R (S q))
    (dgBarDegreeSubcomplexDifferential R K S hS)
    (dgBarDegreeSubcomplexDifferential_squared R K S hS)

def dgBarDegreeSubcomplexInclusion : dgBarDegreeSubcomplex R K S hS ⟶ K :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (S q).subtype) (fun q => by
    dsimp only [dgBarDegreeSubcomplex]
    rw [CochainComplex.of_d]
    rfl)

lemma dgBarDegreeSubcomplexInclusion_injective (q : ℤ) :
    Function.Injective ((dgBarDegreeSubcomplexInclusion R K S hS).f q) :=
  Subtype.val_injective

variable (T : ∀ q : ℤ, Submodule R (K.X q))
  (hT : ∀ (q : ℤ) (z : K.X q), z ∈ T q → K.d q (q + 1) z ∈ T (q + 1))

def dgBarDegreeSubcomplexMap (h : ∀ q, S q ≤ T q) :
    dgBarDegreeSubcomplex R K S hS ⟶ dgBarDegreeSubcomplex R K T hT :=
  CochainComplex.ofHom (fun q => ModuleCat.ofHom (Submodule.inclusion (h q))) (fun q => by
    dsimp only [dgBarDegreeSubcomplex]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    rfl)

lemma dgBarDegreeSubcomplexMap_injective (h : ∀ q, S q ≤ T q) (q : ℤ) :
    Function.Injective ((dgBarDegreeSubcomplexMap R K S hS T hT h).f q) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : T q => z.val) hab)

@[reassoc]
lemma dgBarDegreeSubcomplexMap_inclusion (h : ∀ q, S q ≤ T q) :
    dgBarDegreeSubcomplexMap R K S hS T hT h ≫
      dgBarDegreeSubcomplexInclusion R K T hT = dgBarDegreeSubcomplexInclusion R K S hS := by
  ext q
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
