module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import SerrePositivity.HomologicalAlgebra.CochainTensor.DegreeMaps
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-! # 次数ごとに分裂する短完全列のテンソル

## 概要

次数ごとに分裂する複体の短完全列を（三つの位置のどれでも）テンソルしても短完全であることと、上に有界な平坦な複体とのテンソルを与える。

## 方針

次数ごとの分裂を `CochainTensor/DegreeMaps` で移す。

## 規約

全体の分裂は要求しない。

## 使われ方

PerfectComplex の閉台の K₀ のテンソル、導来テンソル。
-/

@[expose] public noncomputable section

universe u

section CochainTensorShortExactPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

/-- A degreewise retraction with explicit component types. -/
abbrev cochainSplittingRetraction
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ) : S.X₂.X i ⟶ S.X₁.X i := (σ i).r

/-- A degreewise section with explicit component types. -/
abbrev cochainSplittingSection
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (i : ℤ) : S.X₃.X i ⟶ S.X₂.X i := (σ i).s

/-- The consecutive maps of a short complex compose to zero in every degree. -/
lemma cochainShortComplex_f_g (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) :=
  funext fun i => congrArg (fun f => f.f i) S.zero

lemma cochainSplitting_f_r (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) = (fun i => 𝟙 (S.X₁.X i)) :=
  funext fun i => (σ i).f_r

lemma cochainSplitting_s_g (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (fun i => cochainSplittingSection S σ i ≫ S.g.f i) = (fun i => 𝟙 (S.X₃.X i)) :=
  funext fun i => (σ i).s_g

lemma cochainSplitting_id (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i +
      S.g.f i ≫ cochainSplittingSection S σ i) = (fun i => 𝟙 (S.X₂.X i)) :=
  funext fun i => (σ i).id

/-- Tensor a short complex on the right by a fixed cochain complex. -/
abbrev cochainTensorShortComplexRight
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) := S.map (cochainTensorFixedRight Q)

/-- A degreewise splitting induces a degreewise splitting after total tensoring. -/
def cochainTensorShortComplexRightSplitting
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ((cochainTensorShortComplexRight S Q).map (eval _ _ n)).Splitting where
  r := cochainTensorDegreeMap (cochainSplittingRetraction S σ) (fun j => 𝟙 (Q.X j)) n
  s := cochainTensorDegreeMap (cochainSplittingSection S σ) (fun j => 𝟙 (Q.X j)) n
  f_r := by
    change (cochainTensorMap S.f (𝟙 Q)).f n ≫ _ = 𝟙 ((cochainTensor S.X₁ Q).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
    rw [cochainSplitting_f_r, cochainTensorDegreeMap_id]
  s_g := by
    change _ ≫ (cochainTensorMap S.g (𝟙 Q)).f n = 𝟙 ((cochainTensor S.X₃ Q).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [cochainSplitting_s_g, cochainTensorDegreeMap_id]
  id := by
    change cochainTensorDegreeMap (cochainSplittingRetraction S σ) (fun j => 𝟙 (Q.X j)) n ≫
      (cochainTensorMap S.f (𝟙 Q)).f n + (cochainTensorMap S.g (𝟙 Q)).f n ≫
      cochainTensorDegreeMap (cochainSplittingSection S σ) (fun j => 𝟙 (Q.X j)) n =
      𝟙 ((cochainTensor S.X₂ Q).X n)
    rw [← cochainTensorDegreeMap_eq, ← cochainTensorDegreeMap_eq,
      cochainTensorDegreeMap_comp, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [← cochainTensorDegreeMap_add_left]
    rw [cochainSplitting_id, cochainTensorDegreeMap_id]

lemma cochainTensorShortComplexRight_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorShortComplexRight S Q).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (cochainTensorShortComplexRightSplitting S σ Q n).shortExact)

/-- Tensor a short complex on the left by a fixed cochain complex. -/
abbrev cochainTensorShortComplexLeft
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) := S.map (cochainTensorFixedLeft P)

/-- The corresponding degreewise splitting for left tensoring. -/
def cochainTensorShortComplexLeftSplitting
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    ((cochainTensorShortComplexLeft P S).map (eval _ _ n)).Splitting where
  r := cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingRetraction S σ) n
  s := cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingSection S σ) n
  f_r := by
    change (cochainTensorMap (𝟙 P) S.f).f n ≫ _ = 𝟙 ((cochainTensor P S.X₁).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
    rw [cochainSplitting_f_r, cochainTensorDegreeMap_id]
  s_g := by
    change _ ≫ (cochainTensorMap (𝟙 P) S.g).f n = 𝟙 ((cochainTensor P S.X₃).X n)
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [cochainSplitting_s_g, cochainTensorDegreeMap_id]
  id := by
    change cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingRetraction S σ) n ≫
      (cochainTensorMap (𝟙 P) S.f).f n + (cochainTensorMap (𝟙 P) S.g).f n ≫
      cochainTensorDegreeMap (fun i => 𝟙 (P.X i)) (cochainSplittingSection S σ) n =
      𝟙 ((cochainTensor P S.X₂).X n)
    rw [← cochainTensorDegreeMap_eq, ← cochainTensorDegreeMap_eq,
      cochainTensorDegreeMap_comp, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id]
    rw [← cochainTensorDegreeMap_add_right]
    rw [cochainSplitting_id, cochainTensorDegreeMap_id]

lemma cochainTensorShortComplexLeft_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (cochainTensorShortComplexLeft P S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (cochainTensorShortComplexLeftSplitting P S σ n).shortExact)

/-- Short exact sequences with projective quotient terms split in every degree. -/
def cochainDegreewiseSplittingOfProjective
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) (i : ℤ) :
    (S.map (eval _ _ i)).Splitting := by
  have := hS.mono_f
  have := hS.epi_g
  have := hproj i
  letI : Projective ((S.map (eval _ _ i)).X₃) := by
    change Projective (S.X₃.X i)
    infer_instance
  exact (hS.map (eval _ _ i)).splittingOfProjective

lemma cochainTensorShortComplexRight_shortExact_of_projective
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i))
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorShortComplexRight S Q).ShortExact :=
  cochainTensorShortComplexRight_shortExact S (cochainDegreewiseSplittingOfProjective S hS hproj) Q

lemma cochainTensorShortComplexLeft_shortExact_of_projective
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hproj : ∀ i, Module.Projective R (S.X₃.X i)) :
    (cochainTensorShortComplexLeft P S).ShortExact :=
  cochainTensorShortComplexLeft_shortExact P S (cochainDegreewiseSplittingOfProjective S hS hproj)

end SerrePositivity

end CochainTensorShortExactPart

section CochainTensorTripleShortExactPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

abbrev cochainTensorTripleShortComplexFirst
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (Q T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (cochainTensorShortComplexRight S Q) T

abbrev cochainTensorTripleShortComplexSecond
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensorShortComplexRight (cochainTensorShortComplexLeft P S) T

abbrev cochainTensorTripleShortComplexThird
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) :=
  cochainTensorShortComplexLeft (cochainTensor P Q) S

lemma cochainTensorTripleShortComplexFirst_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorTripleShortComplexFirst S Q T).ShortExact :=
  cochainTensorShortComplexRight_shortExact (cochainTensorShortComplexRight S Q)
    (cochainTensorShortComplexRightSplitting S σ Q) T

lemma cochainTensorTripleShortComplexSecond_shortExact
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorTripleShortComplexSecond P S T).ShortExact :=
  cochainTensorShortComplexRight_shortExact (cochainTensorShortComplexLeft P S)
    (cochainTensorShortComplexLeftSplitting P S σ) T

lemma cochainTensorTripleShortComplexThird_shortExact
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) :
    (cochainTensorTripleShortComplexThird P Q S).ShortExact :=
  cochainTensorShortComplexLeft_shortExact (cochainTensor P Q) S σ

end SerrePositivity

end CochainTensorTripleShortExactPart

section CochainTensorBoundedAbovePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Only maps on the diagonal contributing to a total degree need be invertible. -/
lemma cochainTensorMap_f_isIso_of_diagonal
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (n : ℤ)
    (h : ∀ i j : ℤ, i + j = n → IsIso (f.f i ⊗ₘ g.f j)) :
    IsIso ((cochainTensorMap f g).f n) := by
  let v : (cochainTensor P' Q').X n ⟶ (cochainTensor P Q).X n :=
    HomologicalComplex₂.totalDesc _ (fun i j hij =>
      have := h i j hij
      inv (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P Q i j n hij)
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have := h i j hij
    simp only [v, ι_mapBifunctorMap_assoc,
      HomologicalComplex₂.ι_totalDesc, Category.comp_id,
      curriedTensor_map_app, curriedTensor_obj_map]
    simpa only [tensorHom_def, Category.assoc] using
      (IsIso.hom_inv_id_assoc (f.f i ⊗ₘ g.f j) (ιTensorObj P Q i j n hij))
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    have := h i j hij
    simp [v, ι_mapBifunctorMap, tensorHom_def]

/-- Lower truncation preserves a tensor degree if the other factor vanishes above. -/
lemma cochainTensor_truncation_f_isIso
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (a b n : ℤ)
    (hP : ∀ j, b < j → IsZero (P.X j)) (hn : a + b ≤ n) :
    IsIso ((cochainTensorMap (StupidTruncation.inclusion Q a) (𝟙 P)).f n) := by
  apply cochainTensorMap_f_isIso_of_diagonal
  intro i j hij
  by_cases hi : a ≤ i
  · have := StupidTruncation.inclusion_f_isIso Q a i hi
    change IsIso ((StupidTruncation.inclusion Q a).f i ⊗ₘ 𝟙 (P.X j))
    infer_instance
  · have hz := hP j (by omega)
    exact ((tensorLeft ((StupidTruncation.above Q a).X i)).map_isZero hz).isIso
      ((tensorLeft (Q.X i)).map_isZero hz) _

/-- A bounded-above flat complex preserves acyclicity of bounded-above complexes.
No lower bound or finite projective dimension is required. -/
lemma cochainTensor_acyclic_of_flat_boundedAbove
    (Q P : CochainComplex (ModuleCat.{u} R) ℤ) (bQ bP : ℤ)
    (hQ : ∀ i, bQ < i → IsZero (Q.X i))
    (hP : ∀ i, bP < i → IsZero (P.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (hacyclic : P.Acyclic) :
    (cochainTensor Q P).Acyclic := by
  intro n
  let a := n - 1 - bP
  let T := StupidTruncation.above Q a
  have hTa (i : ℤ) (hi : i < a) : IsZero (T.X i) :=
    StupidTruncation.above_isZero_X Q a i hi
  have hTb (i : ℤ) (hi : bQ < i) : IsZero (T.X i) := by
    by_cases hai : a ≤ i
    · exact (StupidTruncation.aboveXIso Q a i hai).isZero_iff.mpr (hQ i hi)
    · exact hTa i (by omega)
  have hTf (i : ℤ) : Module.Flat R (T.X i) := by
    by_cases hai : a ≤ i
    · have := hflat i
      exact Module.Flat.of_linearEquiv (StupidTruncation.aboveXIso Q a i hai).toLinearEquiv
    · have := ModuleCat.subsingleton_of_isZero (hTa i (by omega))
      infer_instance
  have hac := cochainTensor_acyclic_of_flat_bounds T P a bQ hTa hTb hTf hacyclic
  let f := cochainTensorMap (StupidTruncation.inclusion Q a) (𝟙 P)
  have hf (q : ℤ) (hq : n - 1 ≤ q) : IsIso (f.f q) :=
    cochainTensor_truncation_f_isIso Q P a bP q hP (by dsimp [a]; omega)
  have hqi : QuasiIsoAt f n := by
    rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
    let t := (shortComplexFunctor' (ModuleCat.{u} R) (.up ℤ) (n - 1) n (n + 1)).map f
    have : IsIso t.τ₁ := hf (n - 1) (by omega)
    have : IsIso t.τ₂ := hf n (by omega)
    have : IsIso t.τ₃ := hf (n + 1) (by omega)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono t
  exact (quasiIsoAt_iff_exactAt f n (hac n)).mp hqi

/-- A bounded-above flat right factor preserves quasi-isomorphisms between
bounded-above complexes. -/
lemma cochainTensor_quasiIso_left_of_boundedAboveFlat
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (bQ bP bP' : ℤ)
    (hQ : ∀ i, bQ < i → IsZero (Q.X i))
    (hP : ∀ i, bP < i → IsZero (P.X i))
    (hP' : ∀ i, bP' < i → IsZero (P'.X i))
    (hflat : ∀ i, Module.Flat R (Q.X i)) (f : P ⟶ P') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).mp inferInstance
  have hb (i : ℤ) (hi : max bP bP' < i) :
      IsZero ((CochainComplex.mappingCone f).X i) := by
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hP (i + 1) (by omega), hP' i (by omega)⟩
  have ht := cochainTensor_acyclic_of_flat_boundedAbove Q
    (CochainComplex.mappingCone f) bQ (max bP bP') hQ hb hflat hc
  have ht' := cochainAcyclic_of_iso ht (cochainTensorSymmetry Q (CochainComplex.mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).mpr
    (cochainAcyclic_of_iso ht' (cochainTensorConeLeft f Q))

end SerrePositivity

end CochainTensorBoundedAbovePart
