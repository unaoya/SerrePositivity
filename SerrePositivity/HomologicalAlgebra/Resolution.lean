module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# ℤ 添字 cochain 複体と射影分解の行き来

## 概要

このプロジェクトでは複体を ℤ 添字の cochain 複体として扱う。一方、Mathlib の射影分解
`ProjectiveResolution X` は ℕ 添字の chain 複体 `P_0 ← P_1 ← …` であり、左導来関手（`Tor`）の
計算はこの形で行われる。このファイルは二つの形の間を行き来する道具を用意する。対応は
添字 `n ↦ -n`、すなわち chain の `n` 次を cochain の `-n` 次に置く埋め込み `embUp`
（Mathlib の `ComplexShape.embeddingUpIntLE 0`）で与える。

## 内容

1. **制限 `toChain`**：cochain 複体 `K` の `0` 以下の次数だけを取り出して chain 複体にする。
   `K` が `0` 以下の次数に乗っていればホモロジーは保たれる（`toChainHomologyIso`：
   `(toChain K).homology n ≅ K.homology (-n)`）。`n ≥ 1` では Mathlib の `restrictionHomologyIso` が
   そのまま使えるが、`n = 0` は制限の端なので別扱いになり、「`1` 次の項が零なら `0` 次の
   ホモロジーは余サイクル `opcycles` に等しい」ことを両辺で使ってつなぐ。
2. **`IsResolutionOf K Z`**：cochain 複体 `K` が加群 `Z` の分解であること。すなわち `0` 以下の次数に
   乗り、各項が射影的で、`H^i(K) = 0 (i ≠ 0)`、`H^0(K) ≅ Z`。このとき `toChain K` に増大射
   `toChain K → Z[0]`（`IsResolutionOf.π`）を付けると Mathlib の `ProjectiveResolution Z` になる
   （`toProjectiveResolution`）。Koszul 複体を射影分解として使うとき
   （`CommutativeAlgebra/KoszulResolution.lean`）と、持ち上げの写像錐が分解になること
   （`ConeResolution.lean`）に使う。
3. **延長 `extRes`**：逆向きに、Mathlib の射影分解 `P` を `embUp` に沿って cochain 複体に延長する。
   延長した複体は `IsResolutionOf (extRes P) X` をみたす（`isResolutionOf_extRes`）。射 `f : X ⟶ Y` の
   射影分解への持ち上げ `ProjectiveResolution.lift f P Q` も延長でき（`extLift`）、`0` 次のホモロジーで
   `f` を誘導する（`extLift_homologyZero`）。Tor の長完全列（`TorLES.lean`）で、短完全列の射を
   分解の間の鎖写像に持ち上げて写像錐をとるために使う。

階数の計算として、整域上の有限な射影分解の階数の交代和を求める
`resolution_alternating_finrank` も示す。正則局所環に固有の入力には依存しない。

## 規約

`embUp.f n = 0 - n = -n`。制限と延長は Mathlib の `HomologicalComplex.restriction`・`extend` で、
項の同一視は `restrictionXIso`・`extendXIso`、ホモロジーの同一視は `restrictionHomologyIso`・
`extendHomologyIso` を使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 制限 `toChain` -/

/-- 添字の埋め込み `down ℕ → up ℤ`、`n ↦ -n`。Mathlib の `ComplexShape.embeddingUpIntLE 0` で、
chain 複体の `n` 次を cochain 複体の `-n` 次に対応させる。 -/
noncomputable abbrev embUp : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntLE 0

/-- 添字の埋め込み `embUp` は微分の向きを保つ：chain 複体で `n + 1 → n` に微分があることと、
cochain 複体で `-(n+1) → -n` に微分があることが同値。制限・延長のホモロジーの同一視
（`restrictionHomologyIso` など）に要る Mathlib の前提条件。 -/
instance : embUp.IsRelIff := inferInstanceAs (ComplexShape.embeddingUpIntLE 0).IsRelIff

/-- ℤ 添字 cochain 複体 `K` の、`n ↦ -n` に沿った ℕ 添字 chain 複体への制限。`n` 次の項は `K^{-n}`、
微分 `n + 1 → n` は `K` の微分 `K^{-(n+1)} → K^{-n}` で、`K` の正の次数の項は捨てられる。 -/
noncomputable abbrev toChain (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  K.restriction embUp

section toChain

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- `n ≥ 1` でのホモロジーの同型 `(toChain K).homology (n+1) ≅ K.homology (-(n+1))`。
chain 複体の `n + 1` 次の両隣 `n + 2`、`n` は cochain の `-(n+2)`、`-n` に対応し、どちらも制限の
範囲に入っているので、`n + 1` 次のホモロジーを定める短複体が両辺で一致する。したがって Mathlib の
`restrictionHomologyIso` がそのまま使える。 -/
noncomputable def toChainHomologyIsoSucc (n : ℕ) :
    (toChain K).homology (n + 1) ≅ K.homology (-(n + 1 : ℕ) : ℤ) :=
  HomologicalComplex.restrictionHomologyIso K embUp (n + 2) (n + 1) n
    (hi := by simp [ChainComplex.prev]) (hk := ChainComplex.next_nat_succ n)
    (i' := -(n + 2 : ℕ)) (j' := -(n + 1 : ℕ)) (k' := -(n : ℕ))
    (hi' := by simp) (hj' := by simp) (hk' := by simp)
    (hi'' := by rw [CochainComplex.prev]; omega) (hk'' := by rw [CochainComplex.next]; omega)

/-- `K` の `1` 次の項が零なら、微分 `K^0 → K^1` は零射である（零対象への射は一意）。
`0` 次のホモロジーを余サイクルで表すとき（`toChainHomologyIsoZero`）の前提として使う。 -/
lemma d_zero_one_eq_zero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) : K.d 0 1 = 0 :=
  (hK 1 one_pos).eq_of_tgt _ _

/-- `K` が正の次数で零のとき、`0` 次のホモロジーの同型 `(toChain K).homology 0 ≅ K.homology 0`。
`0` 次は制限の端（chain 複体には `-1` 次がない）なので `restrictionHomologyIso` は使えない。
代わりに、出ていく微分が零なら `0` 次のホモロジーは余サイクル `K^0 / im(K^{-1} → K^0)` に等しい
（`isIso_homologyι`）ことを両辺で使い、余サイクルについての Mathlib の同型
`restrictionOpcyclesIso` でつなぐ。 -/
noncomputable def toChainHomologyIsoZero (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    (toChain K).homology 0 ≅ K.homology 0 :=
  haveI : IsIso (K.homologyι 0) :=
    K.isIso_homologyι 0 1 (by simp [CochainComplex.next]) (d_zero_one_eq_zero K hK)
  asIso ((toChain K).homologyι 0) ≪≫
    HomologicalComplex.restrictionOpcyclesIso K embUp (i := 1) (j := 0)
      (hi := by simp [ChainComplex.prev]) (i' := -1) (j' := 0) (hi' := by simp) (hj' := by simp)
      (hi'' := by rw [CochainComplex.prev]; omega) ≪≫
    (asIso (K.homologyι 0)).symm

/-- `K` が正の次数で零のとき、すべての `n : ℕ` で `(toChain K).homology n ≅ K.homology (-n)`。
`n = 0` は `toChainHomologyIsoZero`、`n ≥ 1` は `toChainHomologyIsoSucc` による。制限がホモロジーを
保つ、という主張の最終形で、`Tor` を cochain 分解で計算するとき（`Tor.lean` の `torIsoCochain`）に
使う。 -/
noncomputable def toChainHomologyIso (hK : ∀ i : ℤ, 0 < i → IsZero (K.X i)) :
    ∀ n : ℕ, (toChain K).homology n ≅ K.homology (-(n : ℤ))
  | 0 => toChainHomologyIsoZero K hK ≪≫ eqToIso (by simp)
  | n + 1 => toChainHomologyIsoSucc K n

end toChain

/-- 加法的関手 `F : ModuleCat R ⥤ ModuleCat S` を各項に施す操作は、`n ↦ -n` に沿った制限と
可換である：`F(toChain K) ≅ toChain (F K)`。各項・各微分が定義上同じものなので、成分が恒等射の
同型で与えられる。`Tor` を cochain 分解で計算するとき（`Tor.lean` の `torIsoCochain`）に、係数拡大と
制限の順序を入れ替えるのに使う。 -/
noncomputable def mapRestrictionIso {S : Type u} [CommRing S]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (F.mapHomologicalComplex _).obj (toChain K) ≅ toChain ((F.mapHomologicalComplex _).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _)
    (fun _ _ _ ↦ (Category.id_comp _).trans (Category.comp_id _).symm)

/-! ## cochain 複体からの射影分解 -/

/-- ℤ 添字 cochain 複体 `K` が加群 `Z` の分解であること。`K` は `0` 以下の次数に乗り、各項は
射影的で、ホモロジーは `0` 次に集中し、`H^0(K) ≅ Z`。Mathlib の `ProjectiveResolution` を
cochain 複体の言葉で言い換えたもので、`toProjectiveResolution` で実際に `ProjectiveResolution Z` に
変換できる。Koszul 複体（`IsKoszulResolution`）、持ち上げの写像錐（`isResolutionOf_cone`）、
延長した射影分解（`isResolutionOf_extRes`）がこの条件をみたす。同型 `H^0(K) ≅ Z` をデータとして
もつので `Prop` ではなく `Type` 値の構造体である。 -/
structure IsResolutionOf (K : CochainComplex (ModuleCat.{u} R) ℤ) (Z : ModuleCat.{u} R) where
  /-- 正の次数の項は零。 -/
  isZero_X : ∀ i : ℤ, 0 < i → IsZero (K.X i)
  /-- 各項は射影加群。 -/
  projective : ∀ i : ℤ, Projective (K.X i)
  /-- `0` 以外の次数でホモロジーは零（`K` は `0` 次以外で完全）。 -/
  isZero_homology : ∀ i : ℤ, i ≠ 0 → IsZero (K.homology i)
  /-- `0` 次のホモロジーと `Z` の同型。増大射 `K → Z[0]` を与えるのに使う。 -/
  homologyZeroIso : K.homology 0 ≅ Z

namespace IsResolutionOf

variable {K : CochainComplex (ModuleCat.{u} R) ℤ} {Z : ModuleCat.{u} R} (h : IsResolutionOf K Z)

/-- `toChain K` の `0` 次の余サイクル `K^0 / im(K^{-1} → K^0)` と `Z` の同型。chain 複体の `0` 次は
末端で出ていく微分がないので、余サイクルはホモロジーと一致する（`homologyι 0` が同型）。そこで
`toChainHomologyIsoZero` と `h.homologyZeroIso` を合成する。増大射 `π` の `0` 次成分を定めるのに
使う。 -/
noncomputable def opcyclesIso : (toChain K).opcycles 0 ≅ Z :=
  (asIso ((toChain K).homologyι 0)).symm ≪≫ toChainHomologyIsoZero K h.isZero_X ≪≫
    h.homologyZeroIso

/-- 増大射 `toChain K ⟶ Z[0]`。`0` 次の成分は `K^0 → (0 次の余サイクル) → Z`、他の次数は零。
`0` 次に集中した複体への鎖写像は「`0` 次の成分で、微分 `1 → 0` と合成して零になるもの」と同じ
（Mathlib の `toSingle₀Equiv`）なので、余サイクルへの射影を経由する射を与えればよい。 -/
noncomputable def π : toChain K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom, by
      rw [← Category.assoc, HomologicalComplex.d_pOpcycles, zero_comp]⟩

/-- 増大射 `π` の `0` 次成分は、余サイクルへの射影 `pOpcycles 0` と同型 `opcyclesIso` の合成である
（定義の展開）。`π` が擬同型であることの証明で使う。 -/
lemma π_f_zero : h.π.f 0 = (toChain K).pOpcycles 0 ≫ h.opcyclesIso.hom := by
  simp [π]

/-- 増大射 `π : toChain K → Z[0]` は擬同型である。`0` 次では、両辺の `0` 次ホモロジーが余サイクルと
一致し、`π` が余サイクル上に誘導する射が同型 `opcyclesIso`（と `Z[0]` 側の自明な同型）であることから。
正の次数では、`K` の完全性（`h.isZero_homology`）と `Z[0]` の形から両辺のホモロジーが零なので
自動的に同型。これで `toChain K` が `ProjectiveResolution` の条件をみたす。 -/
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

/-- `toChain K` を、増大射 `π` とともに Mathlib の `ProjectiveResolution Z` とみなす。各項の射影性は、
制限の項が `K` の項と同型であること（`restrictionXIso`）と `h.projective` から。左導来関手の計算
（`ProjectiveResolution.isoLeftDerivedObj`）に渡すための形である。 -/
noncomputable def toProjectiveResolution : ProjectiveResolution Z where
  complex := toChain K
  projective m := Projective.of_iso (K.restrictionXIso embUp rfl).symm (h.projective _)
  π := h.π

end IsResolutionOf

/-! ## 射影分解の延長 -/

section extend

/-- 埋め込み `embUp` は `0` を `0` に送る。延長した複体の `0` 次ホモロジーを同定するときに、
`extendHomologyIso` に渡す添字の条件として使う。 -/
lemma embUp_f_zero : embUp.f 0 = 0 := by
  change (0 : ℤ) - 0 = 0
  simp

variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)

/-- Mathlib の射影分解 `P : ProjectiveResolution X` を、`embUp` に沿って ℤ 添字 cochain 複体に
延長したもの。`-n` 次の項が `P_n`、正の次数の項は零。 -/
noncomputable abbrev extRes : CochainComplex (ModuleCat.{u} R) ℤ :=
  P.complex.extend embUp

/-- 延長した複体 `extRes P` の正の次数の項は零。正の次数は埋め込みの像 `{-n | n : ℕ}` に入らないので、
`extend` の定義から零対象になる（`isZero_extend_X`）。 -/
lemma extRes_isZero_X (i : ℤ) (hi : 0 < i) : IsZero ((extRes P).X i) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ by
    have : (0 : ℤ) - n = i := hn
    omega)

/-- 延長した複体 `extRes P` の各項は射影的。埋め込みの像に入る次数 `-n` では項が `P_n` と同型
（`extendXIso`）で射影的、それ以外の次数では零対象で、零対象は射影的である。 -/
lemma extRes_projective (i : ℤ) : Projective ((extRes P).X i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    exact Projective.of_iso (P.complex.extendXIso embUp rfl).symm (P.projective n)
  · exact (HomologicalComplex.isZero_extend_X _ _ _ (fun n hn ↦ h ⟨n, hn⟩)).projective

/-- 射影分解 `P` の `n ≠ 0` 次のホモロジーは零。増大射 `P.π : P → X[0]` が擬同型なので `P` の
ホモロジーは `X[0]` のホモロジーと同型で、それは `0` 次以外で零だから。 -/
lemma res_homology_isZero (n : ℕ) (hn : n ≠ 0) : IsZero (P.complex.homology n) :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  (asIso (HomologicalComplex.homologyMap P.π n)).isZero_iff.mpr
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn)

/-- 延長した複体 `extRes P` の `0` 以外の次数のホモロジーは零。埋め込みの像の次数 `-n`（`n ≠ 0`）では
`res_homology_isZero` を `extendHomologyIso` で移し、像の外の次数では延長した複体が完全であること
（`extend_exactAt`）による。 -/
lemma extRes_isZero_homology (i : ℤ) (hi : i ≠ 0) : IsZero ((extRes P).homology i) := by
  by_cases h : ∃ n : ℕ, embUp.f n = i
  · obtain ⟨n, rfl⟩ := h
    refine (P.complex.extendHomologyIso embUp rfl).isZero_iff.mpr (res_homology_isZero P n ?_)
    rintro rfl
    exact hi rfl
  · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (HomologicalComplex.extend_exactAt _ _ _ (fun n hn ↦ h ⟨n, hn⟩))

/-- 延長した複体 `extRes P` の `0` 次ホモロジーと `X` の同型。`extendHomologyIso` で `P` の `0` 次
ホモロジーに移し、擬同型 `P.π` で `X[0]` の `0` 次ホモロジーに移し、それを `X` と同一視する
（`singleObjHomologySelfIso`）。 -/
noncomputable def extResHomologyZeroIso : (extRes P).homology 0 ≅ X :=
  haveI : IsIso (HomologicalComplex.homologyMap P.π 0) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  P.complex.extendHomologyIso embUp (j := 0) (j' := 0) embUp_f_zero ≪≫
    asIso (HomologicalComplex.homologyMap P.π 0) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 X

/-- 延長した射影分解は `IsResolutionOf (extRes P) X` をみたす。上の四つ（正の次数で零、各項が射影的、
`0` 次以外でホモロジーが零、`H^0 ≅ X`）をまとめたもの。 -/
noncomputable def isResolutionOf_extRes : IsResolutionOf (extRes P) X where
  isZero_X := extRes_isZero_X P
  projective := extRes_projective P
  isZero_homology := extRes_isZero_homology P
  homologyZeroIso := extResHomologyZeroIso P

/-- 射 `f : X ⟶ Y` と射影分解 `P`、`Q` について、Mathlib の持ち上げ `ProjectiveResolution.lift f P Q`
（`f` と両立する鎖写像 `P → Q`）を延長した鎖写像 `extRes P ⟶ extRes Q`。短完全列の射を分解の間の
鎖写像にして写像錐をとるとき（`ConeResolution.lean` の `liftSES`）に使う。 -/
noncomputable abbrev extLift {Y : ModuleCat.{u} R} (f : X ⟶ Y) (Q : ProjectiveResolution Y) :
    extRes P ⟶ extRes Q :=
  HomologicalComplex.extendMap (ProjectiveResolution.lift f P Q) embUp

/-- 持ち上げの延長 `extLift P f Q` は、`0` 次のホモロジーで `f` を誘導する：両辺の `0` 次ホモロジーを
`extResHomologyZeroIso` で `X`、`Y` と同一視すると `f` になる。`extendHomologyIso` の自然性、持ち上げが
増大射と可換であること（`lift_commutes`）、`single₀` のホモロジーの同一視の自然性を順につなぐ。 -/
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

/-- 加法的関手の左導来関手を、任意の射影コチェイン分解で計算する。
Mathlib の `ProjectiveResolution.isoLeftDerivedObj` を使い、自然数添字の鎖複体と
整数添字のコチェイン複体を同一視する。右完全性、有限生成性、有界性は不要である。 -/
noncomputable def leftDerivedIsoCochain {S : Type u} [CommRing S]
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {Z : ModuleCat.{u} R} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : IsResolutionOf K Z) (i : ℕ) :
    (G.leftDerived i).obj Z ≅ ((G.mapHomologicalComplex _).obj K).homology (-(i : ℤ)) :=
  h.toProjectiveResolution.isoLeftDerivedObj G i ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (mapRestrictionIso G K) ≪≫
    toChainHomologyIso _ (fun j hj => G.map_isZero (h.isZero_X j hj)) i

/-- 左側で有界な射影コチェイン分解があれば、任意の加法的関手の高次左導来関手は消える。
`K^j = 0 (j < a)` なら、`i > max(0,-a)` で計算に使う `K^{-i}` が零になる。
正則局所環や有限生成性に依存せず、有界な分解そのものを仮定として受け取る。 -/
theorem isZero_leftDerived_eventually_of_resolution {S : Type u} [CommRing S]
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {Z : ModuleCat.{u} R} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : IsResolutionOf K Z) (a : ℤ) (ha : ∀ j, j < a → IsZero (K.X j)) :
    ∃ n : ℕ, ∀ i : ℕ, n < i → IsZero ((G.leftDerived i).obj Z) := by
  refine ⟨(-a).toNat, fun i hi => ?_⟩
  apply (leftDerivedIsoCochain G h i).isZero_iff.mpr
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ (G.map_isZero (ha _ (by omega)))

/-- 加法的関手の左導来関手も加法的である。
二つの射を同じ射影分解の間に持ち上げ、その和が和の持ち上げになることから従う。 -/
instance leftDerived_additive {C D : Type*} [Category* C] [Abelian C]
    [HasProjectiveResolutions C] [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive] (i : ℕ) :
    (F.leftDerived i).Additive where
  map_add {X Y} f g := by
    let P := projectiveResolution X
    let Q := projectiveResolution Y
    let f' := ProjectiveResolution.lift f P Q
    let g' := ProjectiveResolution.lift g P Q
    have hf : f' ≫ Q.π = P.π ≫ (ChainComplex.single₀ _).map f :=
      ProjectiveResolution.lift_commutes f P Q
    have hg : g' ≫ Q.π = P.π ≫ (ChainComplex.single₀ _).map g :=
      ProjectiveResolution.lift_commutes g P Q
    have hfg : (f' + g') ≫ Q.π = P.π ≫ (ChainComplex.single₀ _).map (f + g) := by
      rw [Preadditive.add_comp, hf, hg, Functor.map_add, Preadditive.comp_add]
    rw [F.leftDerived_map_eq i (f + g) (f' + g') hfg,
      F.leftDerived_map_eq i f f' hf, F.leftDerived_map_eq i g g' hg,
      Functor.map_add]
    erw [Preadditive.add_comp, Preadditive.comp_add]

/-- 関手が環準同型 `φ` に沿って射のスカラー倍と両立すれば、その左導来関手も同じ性質をもつ。
射影分解の間の持ち上げをスカラー倍し、ホモロジー上のスカラー作用と比較する。 -/
theorem leftDerived_map_smul {S : Type u} [CommRing S] (φ : R →+* S)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    (hF : ∀ {X Y : ModuleCat.{u} R} (a : R) (f : X ⟶ Y), F.map (a • f) = φ a • F.map f)
    (i : ℕ) {X Y : ModuleCat.{u} R} (a : R) (f : X ⟶ Y) :
    (F.leftDerived i).map (a • f) = φ a • (F.leftDerived i).map f := by
  let P := projectiveResolution X
  let Q := projectiveResolution Y
  let g := ProjectiveResolution.lift f P Q
  have hw : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map f :=
    ProjectiveResolution.lift_commutes f P Q
  have hwa : (a • g) ≫ Q.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{u} R)).map (a • f) := by
    rw [single_map_smul, Linear.smul_comp, Linear.comp_smul, hw]
  have hmap : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (a • g) =
      φ a • (F.mapHomologicalComplex _).map g := by
    apply HomologicalComplex.hom_ext
    intro j
    exact hF a (g.f j)
  rw [F.leftDerived_map_eq i (a • f) (a • g) hwa,
    F.leftDerived_map_eq i f g hw, Functor.comp_map, hmap,
    HomologicalComplex.homologyFunctor_map, homologyMap_smul]
  erw [Linear.smul_comp, Linear.comp_smul]
  rfl

/-- `a` が加群 `X` を消すとき、スカラー倍と両立する加法的関手の
左導来関手の値は `φ(a)` で消える。導来関手の加法性とスカラー倍の保存による。 -/
theorem leftDerived_smul_eq_zero {S : Type u} [CommRing S] (φ : R →+* S)
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
    (hF : ∀ {X Y : ModuleCat.{u} R} (a : R) (f : X ⟶ Y), F.map (a • f) = φ a • F.map f)
    (i : ℕ) (X : ModuleCat.{u} R) (a : R) (ha : ∀ x : X, a • x = 0)
    (x : (F.leftDerived i).obj X) : φ a • x = 0 := by
  have hz : (a • 𝟙 X : X ⟶ X) = 0 := ModuleCat.hom_ext (LinearMap.ext ha)
  have h := leftDerived_map_smul φ F hF i a (𝟙 X)
  rw [hz, Functor.map_zero, CategoryTheory.Functor.map_id] at h
  exact (congrArg (fun f : (F.leftDerived i).obj X ⟶ (F.leftDerived i).obj X => f.hom x) h).symm

end SerrePositivity

namespace SerrePositivity

variable {R : Type u} [CommRing R] [IsDomain R]
/-- 整域上の完全列の中央の有限生成加群の階数は、前後の射の像の階数の和である。
Mathlib の商加群に対する rank-nullity と第一同型定理による。 -/
lemma finrank_eq_add_range_of_exact {M N L : ModuleCat.{u} R}
    [Module.Finite R N] (f : M ⟶ N) (g : N ⟶ L) (he : Function.Exact f.hom g.hom) :
    Module.finrank R N = Module.finrank R (LinearMap.range f.hom) +
      Module.finrank R (LinearMap.range g.hom) := by
  have h := (LinearMap.ker g.hom).finrank_quotient_add_finrank
  rw [g.hom.quotKerEquivRange.finrank_eq, LinearMap.exact_iff.mp he] at h
  omega

/-- 整域上の射影分解の各項が有限生成で、`n + 1` 次の項が零なら、
`0` 次から `n` 次までの階数の交代和は分解される加群の階数に等しい。
微分の像の階数を用いて完全列の加法性を足し合わせる。自由性や正則局所性は不要。 -/
lemma resolution_alternating_finrank {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (hfinite : ∀ i, Module.Finite R (P.complex.X i))
    (n : ℕ) (hz : IsZero (P.complex.X (n + 1))) :
    (∑ i ∈ Finset.range (n + 1), (-1 : ℝ)^i * Module.finrank R (P.complex.X i)) =
      Module.finrank R M := by
  let r := fun i => (Module.finrank R (LinearMap.range (P.complex.d (i + 1) i).hom) : ℝ)
  have e0 : (Module.finrank R (P.complex.X 0) : ℝ) = Module.finrank R M + r 0 := by
    have := hfinite 0
    have h := finrank_eq_add_range_of_exact (P.complex.d 1 0) (P.π.f 0)
      (LinearMap.exact_iff.mpr P.exact₀.moduleCat_range_eq_ker.symm)
    have hs : Function.Surjective (P.π.f 0).hom := (ModuleCat.epi_iff_surjective _).mp inferInstance
    rw [LinearMap.range_eq_top.mpr hs] at h
    have ht : Module.finrank R (⊤ : Submodule R M) = Module.finrank R M :=
      (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).finrank_eq
    change Module.finrank R (P.complex.X 0) = _ + Module.finrank R (⊤ : Submodule R M) at h
    rw [ht] at h
    dsimp [r]
    exact_mod_cast h.trans (Nat.add_comm _ _)
  have es (i : ℕ) : (Module.finrank R (P.complex.X (i + 1)) : ℝ) = r i + r (i + 1) := by
    have := hfinite (i + 1)
    have h := finrank_eq_add_range_of_exact (P.complex.d (i + 2) (i + 1))
      (P.complex.d (i + 1) i)
      (LinearMap.exact_iff.mpr (P.exact_succ i).moduleCat_range_eq_ker.symm)
    dsimp [r]
    exact_mod_cast h.trans (Nat.add_comm _ _)
  have hs : ∀ k, (∑ i ∈ Finset.range (k + 1), (-1 : ℝ)^i * Module.finrank R (P.complex.X i)) =
      Module.finrank R M + (-1 : ℝ)^k * r k := by
    intro k
    induction k with
    | zero => simpa using e0
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, es k, pow_succ]
      ring
  have hr : r n = 0 := by
    have := ModuleCat.subsingleton_of_isZero hz
    have : Subsingleton (LinearMap.range (P.complex.d (n + 1) n).hom) :=
      (P.complex.d (n + 1) n).hom.surjective_rangeRestrict.subsingleton
    simp [r, Module.finrank_zero_of_subsingleton]
  simpa [hr] using hs n
end SerrePositivity

@[expose] public section

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 射影分解の syzygy と短完全列 -/

namespace ResolutionSyzygy
variable {M : ModuleCat.{u} R} (P : ProjectiveResolution M)
/-- 射影分解の第 `i` syzygy。0 次は分解される加群、`i + 1` 次は
微分 `Pᵢ₊₁ → Pᵢ` の像であり、完全性から前の射の核にも等しい。 -/
noncomputable def obj : ℕ → ModuleCat.{u} R
  | 0 => M
  | i + 1 => ModuleCat.of R (LinearMap.range (P.complex.d (i + 1) i).hom)
/-- 次の syzygy を分解の第 `i` 項に埋め込む射。 -/
noncomputable def ι (i : ℕ) : obj P (i + 1) ⟶ P.complex.X i :=
  ModuleCat.ofHom (LinearMap.range (P.complex.d (i + 1) i).hom).subtype
/-- 分解の第 `i` 項から syzygy への全射。0 次では添加写像、
正次数では微分の余域をその像に制限した写像である。 -/
noncomputable def π : ∀ i, P.complex.X i ⟶ obj P i
  | 0 => P.π.f 0
  | i + 1 => ModuleCat.ofHom (P.complex.d (i + 1) i).hom.rangeRestrict
/-- `Zᵢ₊₁ → Pᵢ → Zᵢ` は中央で完全。元の分解の完全性を像への制限に移す。 -/
lemma exact (i : ℕ) : Function.Exact (ι P i).hom (π P i).hom := by
  cases i with
  | zero =>
    rw [LinearMap.exact_iff]
    change (P.π.f 0).hom.ker = (LinearMap.range (P.complex.d 1 0).hom).subtype.range
    rw [Submodule.range_subtype]
    exact P.exact₀.moduleCat_range_eq_ker.symm
  | succ i =>
    rw [LinearMap.exact_iff]
    change (P.complex.d (i + 1) i).hom.rangeRestrict.ker =
      (LinearMap.range (P.complex.d (i + 2) (i + 1)).hom).subtype.range
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
    exact (P.exact_succ i).moduleCat_range_eq_ker.symm
/-- syzygy の包含射は単射。 -/
lemma injective_ι (i : ℕ) : Function.Injective (ι P i).hom := Subtype.val_injective
/-- 分解の各項から syzygy への射は全射。 -/
lemma surjective_π (i : ℕ) : Function.Surjective (π P i).hom := by
  cases i with
  | zero => exact (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance
  | succ i => exact (P.complex.d (i + 1) i).hom.surjective_rangeRestrict
/-- 分解の `n + 1` 次の項が零なら、その像である syzygy も零。
有限分解に沿った降下帰納法の出発点になる。 -/
lemma isZero_obj_succ (n : ℕ) (hz : IsZero (P.complex.X (n + 1))) : IsZero (obj P (n + 1)) := by
  have := ModuleCat.subsingleton_of_isZero hz
  have : Subsingleton (obj P (n + 1)) :=
    (P.complex.d (n + 1) n).hom.surjective_rangeRestrict.subsingleton
  exact ModuleCat.isZero_of_subsingleton _
end ResolutionSyzygy

end SerrePositivity

end
