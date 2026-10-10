module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# ℤ 添字 cochain 複体と射影分解の行き来

埋め込み `embUp : n ↦ -n`（`ComplexShape.embeddingUpIntLE 0`）に沿って、`0` 以下の次数に乗る
ℤ 添字 cochain 複体と、ℕ 添字 chain 複体（Mathlib の `ProjectiveResolution` の形）を行き来する。

## 制限 `toChain`

`toChain K = K.restriction embUp`。`K` が `0` 以下の次数に乗るとき、ホモロジーは保たれる：

- `toChainHomologyIsoSucc`：`n ≥ 1` で `(toChain K).homology n ≅ K.homology (-n)`
  （Mathlib の `restrictionHomologyIso`）。
- `toChainHomologyIsoZero`：`K.X i = 0 (i > 0)` なら `(toChain K).homology 0 ≅ K.homology 0`。
  どちらも `opcycles` と同型なので、`restrictionOpcyclesIso` を経由する。
- `toChainHomologyIso`：両者をまとめたもの。
- `mapRestrictionIso`：加法的関手は制限と両立する。

## cochain 複体からの射影分解 `IsResolutionOf`

`K` が `0` 以下の次数に乗り、各項が射影的で、`H^i(K) = 0 (i ≠ 0)`、`H^0(K) ≅ Z` のとき
（`IsResolutionOf K Z`）、`toChain K` は `Z` の `ProjectiveResolution` になる
（`IsResolutionOf.toProjectiveResolution`）。Koszul 複体
（`CommutativeAlgebra/KoszulResolution.lean`）と、射影分解の持ち上げの写像錐
（`ConeResolution.lean`、`TorLES.lean`）に使う。

## 射影分解の延長 `extRes`

`P : ProjectiveResolution X` に対して `extRes P := P.complex.extend embUp` は
`IsResolutionOf (extRes P) X` をみたす。また射 `f : X ⟶ Y` の持ち上げ `lift f P Q` の延長
`extLift P f Q` は、`H^0(extRes P) ≅ X`、`H^0(extRes Q) ≅ Y` のもとで `f` に対応する。
Tor の長完全列（`TorLES.lean`）で、持ち上げの写像錐をとるために使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 制限 `toChain` -/

/-- 埋め込み `down ℕ → up ℤ`、`n ↦ -n`。 -/
noncomputable abbrev embUp : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE 0

/-- 添字の埋め込みは、チェインとコチェインの微分が許される隣接関係を対応させる。 -/
instance : embUp.IsRelIff := inferInstanceAs (ComplexShape.embeddingUpIntLE 0).IsRelIff

/-- ℤ 添字の cochain 複体の、`n ↦ -n` に沿った ℕ 添字の chain 複体への制限。 -/
noncomputable abbrev toChain (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  K.restriction embUp

section toChain

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- `n ≥ 1` でのホモロジーの同型。 -/
noncomputable def toChainHomologyIsoSucc (n : ℕ) :
    (toChain K).homology (n + 1) ≅ K.homology (-(n + 1 : ℕ) : ℤ) :=
  HomologicalComplex.restrictionHomologyIso K embUp (n + 2) (n + 1) n
    (hi := by simp [ChainComplex.prev]) (hk := ChainComplex.next_nat_succ n)
    (i' := -(n + 2 : ℕ)) (j' := -(n + 1 : ℕ)) (k' := -(n : ℕ))
    (hi' := by simp) (hj' := by simp) (hk' := by simp)
    (hi'' := by rw [CochainComplex.prev]; omega) (hk'' := by rw [CochainComplex.next]; omega)

/-- `K.X 1 = 0` なら `K.d 0 1 = 0`。 -/
lemma d_zero_one_eq_zero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) : K.d 0 1 = 0 :=
  (hK 1 one_pos).eq_of_tgt _ _

/-- `K.X 1 = 0` のとき、`0` 次のホモロジーの同型。 -/
noncomputable def toChainHomologyIsoZero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    (toChain K).homology 0 ≅ K.homology 0 :=
  haveI : IsIso (K.homologyι 0) :=
    K.isIso_homologyι 0 1 (by simp [CochainComplex.next]) (d_zero_one_eq_zero K hK)
  asIso ((toChain K).homologyι 0) ≪≫
    HomologicalComplex.restrictionOpcyclesIso K embUp (i := 1) (j := 0)
      (hi := by simp [ChainComplex.prev]) (i' := -1) (j' := 0) (hi' := by simp) (hj' := by simp)
      (hi'' := by rw [CochainComplex.prev]; omega) ≪≫
    (asIso (K.homologyι 0)).symm

/-- `K.X i = 0 (i > 0)` のとき、すべての `n` で `(toChain K).homology n ≅ K.homology (-n)`。 -/
noncomputable def toChainHomologyIso (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    ∀ n : ℕ, (toChain K).homology n ≅ K.homology (-(n : ℤ))
  | 0 => toChainHomologyIsoZero K hK ≪≫ eqToIso (by simp)
  | n + 1 => toChainHomologyIsoSucc K n

end toChain

/-- 加法的関手は `n ↦ -n` に沿った制限と両立する（各項・各微分は定義上同じ）。 -/
noncomputable def mapRestrictionIso {S : Type u} [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (F.mapHomologicalComplex _).obj (toChain K) ≅ toChain ((F.mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun _ _ _ ↦ (Category.id_comp _).trans (Category.comp_id _).symm)

/-! ## cochain 複体からの射影分解 -/

/-- ℤ 添字 cochain 複体 `K` が `Z` の分解であること。 -/
structure IsResolutionOf (K : CochainComplex (ModuleCat.{u} R) ℤ) (Z : ModuleCat.{u} R) where
  /-- 正の次数で零。 -/
  isZero_X : ∀ i : ℤ, 0 < i → IsZero (K.X i)
  /-- 各項は射影的。 -/
  projective : ∀ i : ℤ, Projective (K.X i)
  /-- `i ≠ 0` でホモロジーは零。 -/
  isZero_homology : ∀ i : ℤ, i ≠ 0 → IsZero (K.homology i)
  /-- 零次ホモロジーを、分解される加群 `Z` に同一視する同型。 -/
  homologyZeroIso : K.homology 0 ≅ Z

namespace IsResolutionOf

variable {K : CochainComplex (ModuleCat.{u} R) ℤ} {Z : ModuleCat.{u} R} (h : IsResolutionOf K Z)

/-- コチェイン分解をチェイン複体に制限したときの零次の余サイクルを、分解される加群に同一視する。 -/
noncomputable def opcyclesIso : (toChain K).opcycles 0 ≅ Z :=
  (asIso ((toChain K).homologyι 0)).symm ≪≫ toChainHomologyIsoZero K h.isZero_X ≪≫
    h.homologyZeroIso

/-- 増大射 `toChain K ⟶ Z`（0 次に集中）。 -/
noncomputable def π : toChain K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom, by
      rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp]⟩

/-- 射影分解の添加写像の零次成分は、零次の余サイクルへの射と分解先への同型の合成である。 -/
lemma π_f_zero : h.π.f 0 = (toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom := by
  simp [π]

/-- 増大射は擬同型。 -/
instance π_quasiIso : QuasiIso h.π where
  quasiIsoAt m := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    cases m with
    | zero =>
      have h1 : HomologicalComplex.opcyclesMap h.π 0 =
          h.opcyclesIso.hom ≫ ((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).pOpcycles 0 := by
        rw [← cancel_epi ((toChain K).pOpcycles 0), HomologicalComplex.p_opcyclesMap, π_f_zero]
        exact Category.assoc _ _ _
      have : IsIso (HomologicalComplex.opcyclesMap h.π 0) := by
        rw [h1]
        exact IsIso.comp_isIso' inferInstance
          (HomologicalComplex.isIso_pOpcycles _ 1 0 (by simp [ChainComplex.prev])
            (HomologicalComplex.single_obj_d _ _ _ _ _))
      have h2 := HomologicalComplex.homologyι_naturality h.π 0
      have : IsIso (HomologicalComplex.homologyMap h.π 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).homologyι 0) := by
        rw [h2]; infer_instance
      exact IsIso.of_isIso_comp_right _
        (((ChainComplex.single₀ (ModuleCat.{u} R)).obj _).homologyι 0)
    | succ m =>
      refine IsZero.isIso ?_ ?_ _
      · exact (toChainHomologyIsoSucc _ m).isZero_iff.mpr (h.isZero_homology _ (by omega))
      · exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ (by omega)

/-- `toChain K` は `Z` の射影分解。 -/
noncomputable def toProjectiveResolution : ProjectiveResolution Z where
  complex := toChain K
  projective m := Projective.of_iso (K.restrictionXIso embUp rfl).symm (h.projective _)
  π := h.π

end IsResolutionOf

/-! ## 射影分解の延長 -/

section extend

/-- 添字の埋め込み `n ↦ -n` は零を零に送る。 -/
lemma embUp_f_zero : embUp.f 0 = 0 := by
  change (0 : ℤ) - 0 = 0
  simp

variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)

/-- 射影分解の ℤ 添字 cochain 複体への延長。 -/
noncomputable abbrev extRes : CochainComplex (ModuleCat.{u} R) ℤ :=
  P.complex.extend embUp

/-- 自然数添字の射影分解を整数添字へ延長した複体は、正次数の項が零になる。 -/
lemma extRes_isZero_X (i : ℤ) (hi : 0 < i) : IsZero ((extRes P).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ by
    have : (0 : ℤ) - n = i := hn
    omega)

/-- 射影分解を整数添字に延長しても、各項は射影的である。追加される項は零対象である。 -/
lemma extRes_projective (i : ℤ) : Projective ((extRes P).X i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    exact Projective.of_iso (P.complex.extendXIso embUp rfl).symm (P.projective n)
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ h ⟨n, hn⟩)).projective

/-- `H_n(P) = 0 (n ≠ 0)`：`π` が擬同型なので。 -/
lemma res_homology_isZero (n : ℕ) (hn : n ≠ 0) : IsZero (P.complex.homology n) :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap P.π n)).isZero_iff.mpr
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)

/-- 整数添字に延長した射影分解のホモロジーは、零次以外で消える。 -/
lemma extRes_isZero_homology (i : ℤ) (hi : i ≠ 0) : IsZero ((extRes P).homology i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    refine (P.complex.extendHomologyIso embUp rfl).isZero_iff.mpr (res_homology_isZero P n ?_)
    rintro rfl
    exact hi rfl
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (HomologicalComplex.extend_exactAt _ _ _ (fun n hn ↦ h ⟨n, hn⟩))

/-- 整数添字に延長した射影分解の零次ホモロジーを、もとの加群に同一視する。 -/
noncomputable def extResHomologyZeroIso : (extRes P).homology 0 ≅ X :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  P.complex.extendHomologyIso embUp (j := 0) (j' := 0) embUp_f_zero ≪≫
    asIso (HomologicalComplex.homologyMap P.π 0) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X

/-- `extRes P` は `X` の分解。 -/
noncomputable def isResolutionOf_extRes : IsResolutionOf (extRes P) X where
  isZero_X := extRes_isZero_X P
  projective := extRes_projective P
  isZero_homology := extRes_isZero_homology P
  homologyZeroIso := extResHomologyZeroIso P

/-- 持ち上げの延長。 -/
noncomputable abbrev extLift {Y : ModuleCat.{u} R} (f : X ⟶ Y) (Q : ProjectiveResolution Y) :
    extRes P ⟶ extRes Q :=
  HomologicalComplex.extendMap (ProjectiveResolution.lift f P Q) embUp

/-- 持ち上げの延長は `H^0` で `f` に対応する。 -/
lemma extLift_homologyZero {Y : ModuleCat.{u} R} (f : X ⟶ Y) (Q : ProjectiveResolution Y) :
    HomologicalComplex.homologyMap (extLift P f Q) 0 ≫ (extResHomologyZeroIso Q).hom =
      (extResHomologyZeroIso P).hom ≫ f := by
  have h1 := HomologicalComplex.extendHomologyIso_hom_naturality
    (ProjectiveResolution.lift f P Q) embUp (j := 0) (j' := 0) embUp_f_zero
  have h2 : HomologicalComplex.homologyMap (ProjectiveResolution.lift f P Q) 0 ≫
      HomologicalComplex.homologyMap Q.π 0 =
      HomologicalComplex.homologyMap P.π 0 ≫
        HomologicalComplex.homologyMap ((ChainComplex.single₀ (ModuleCat.{u} R)).map f) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ProjectiveResolution.lift_commutes,
      HomologicalComplex.homologyMap_comp]
  have h3 := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.down ℕ) 0 f
  simp only [extResHomologyZeroIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, h1, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (ProjectiveResolution.lift f P Q) 0), h2, Category.assoc,
    Category.assoc, h3]
  simp only [Category.assoc]

end extend

end SerrePositivity
