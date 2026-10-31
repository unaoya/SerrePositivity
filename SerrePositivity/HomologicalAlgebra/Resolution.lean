module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
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
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! # ℤ 添字の cochain 分解と射影分解

## 概要

このプロジェクトの ℤ 添字 cochain 複体の分解 `IsResolutionOf` と、Mathlib の ℕ 添字の射影分解 `ProjectiveResolution` を行き来する（chain の n 次を cochain の -n 次に置く）。分解の間の射から誘導される左導来関手の射の自然性、分解の写像の写像錐が余核の分解になること（`isResolutionOf_cone`、馬蹄補題の代わり）、有界な射影分解が射影次元を抑えることを示す。

## 方針

ホモロジーの同型は `embUp` と制限関手の比較で取り、自然性は零次ホモロジーで指定した写像から従う。

## 規約

`coneHomologyZeroEquiv` は ResolutionMappingCone と ConeResolution の両方にあり、後者は前者の特殊化（一本化の候補、refactor-plan §3.2.3）。

## 使われ方

Tor の計算と長完全列、正則局所環の有限自由分解、交点重複度。
-/

@[expose] public noncomputable section

universe u

section ResolutionPart

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


end ResolutionPart

section ResolutionNaturalityPart

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 自然数添字への制限における余サイクルの比較。 -/
noncomputable abbrev toChainOpcyclesIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    (toChain K).opcycles n ≅ K.opcycles (-(n : ℤ)) :=
  K.restrictionOpcyclesIso embUp (i := n + 1) (j := n) (hi := by simp [ChainComplex.prev])
    (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) (hi' := by simp) (hj' := by simp)
    (hi'' := by simp [CochainComplex.prev]; omega)

@[reassoc]
lemma toChainHomologyIso_hom_homologyι (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (n : ℕ) :
    (toChainHomologyIso K hK n).hom ≫ K.homologyι (-(n : ℤ)) =
      (toChain K).homologyι n ≫ (toChainOpcyclesIso K n).hom := by
  cases n with
  | zero =>
    have := K.isIso_homologyι 0 1 (by simp) (d_zero_one_eq_zero K hK)
    simp [toChainHomologyIso, toChainHomologyIsoZero, toChainOpcyclesIso]
  | succ n =>
    exact restrictionHomologyIso_hom_homologyι ..

@[reassoc]
lemma toChainOpcyclesIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℕ) :
    opcyclesMap (restrictionMap f embUp) n ≫ (toChainOpcyclesIso L n).hom =
      (toChainOpcyclesIso K n).hom ≫ opcyclesMap f (-(n : ℤ)) := by
  apply (cancel_epi ((toChain K).pOpcycles n)).mp
  simp only [p_opcyclesMap_assoc, toChainOpcyclesIso,
    pOpcycles_restrictionOpcyclesIso_hom, pOpcycles_restrictionOpcyclesIso_hom_assoc,
    p_opcyclesMap]
  rw [restrictionMap_f' f embUp (by simp : embUp.f n = -(n : ℤ))]
  simp

/-- ホモロジーの添字変換は、分解の射と可換である。 -/
@[reassoc]
lemma toChainHomologyIso_hom_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hK : ∀ q : ℤ, 0 < q → IsZero (K.X q)) (hL : ∀ q : ℤ, 0 < q → IsZero (L.X q)) (n : ℕ) :
    homologyMap (restrictionMap f embUp) n ≫ (toChainHomologyIso L hL n).hom =
      (toChainHomologyIso K hK n).hom ≫ homologyMap f (-(n : ℤ)) := by
  apply (cancel_mono (L.homologyι (-(n : ℤ)))).mp
  simp only [Category.assoc, toChainHomologyIso_hom_homologyι,
    homologyι_naturality, homologyι_naturality_assoc,
    toChainHomologyIso_hom_homologyι_assoc, toChainOpcyclesIso_hom_naturality]

/-- 分解の零次ホモロジーでの両立から、自然数添字の増大射との両立を得る。 -/
lemma IsResolutionOf.restrictionMap_π_f_zero
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {X Y : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (hL : IsResolutionOf L Y) (f : K ⟶ L) (g : X ⟶ Y)
    (h : homologyMap f 0 ≫ hL.homologyZeroIso.hom = hK.homologyZeroIso.hom ≫ g) :
    (restrictionMap f embUp).f 0 ≫ hL.π.f 0 = hK.π.f 0 ≫ g := by
  have he : opcyclesMap (restrictionMap f embUp) 0 ≫ hL.opcyclesIso.hom =
      hK.opcyclesIso.hom ≫ g := by
    apply (cancel_epi ((toChain K).homologyι 0)).mp
    simp only [IsResolutionOf.opcyclesIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
      ← homologyι_naturality_assoc, Category.assoc]
    simp only [IsIso.hom_inv_id_assoc]
    have hn : homologyMap (restrictionMap f embUp) 0 ≫ (toChainHomologyIsoZero L hL.isZero_X).hom =
        (toChainHomologyIsoZero K hK.isZero_X).hom ≫ homologyMap f 0 := by
      simpa [toChainHomologyIso] using
        toChainHomologyIso_hom_naturality f hK.isZero_X hL.isZero_X 0
    rw [← Category.assoc, hn, Category.assoc, h]
  rw [IsResolutionOf.π_f_zero, IsResolutionOf.π_f_zero, ← Category.assoc,
    ← p_opcyclesMap, Category.assoc, he, Category.assoc]

/-- 関手と添字制限の比較は、複体の射と可換である。 -/
@[reassoc]
lemma mapRestrictionIso_hom_naturality (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (G.mapHomologicalComplex _).map (restrictionMap f embUp) ≫ (mapRestrictionIso G L).hom =
      (mapRestrictionIso G K).hom ≫ restrictionMap ((G.mapHomologicalComplex _).map f) embUp := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [mapRestrictionIso]

/-- コチェイン分解で計算した射は、左導来関手の標準の射と一致する。 -/
@[reassoc]
lemma leftDerivedIsoCochain_hom_naturality
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [G.Additive]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {X Y : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (hL : IsResolutionOf L Y) (f : K ⟶ L) (g : X ⟶ Y)
    (h : homologyMap f 0 ≫ hL.homologyZeroIso.hom = hK.homologyZeroIso.hom ≫ g) (i : ℕ) :
    (G.leftDerived i).map g ≫ (leftDerivedIsoCochain G hL i).hom =
      (leftDerivedIsoCochain G hK i).hom ≫
        homologyMap ((G.mapHomologicalComplex _).map f) (-(i : ℤ)) := by
  have hn := ProjectiveResolution.isoLeftDerivedObj_hom_naturality g
    hK.toProjectiveResolution hL.toProjectiveResolution (restrictionMap f embUp)
    (hK.restrictionMap_π_f_zero hL f g h) G i
  have hr := congrArg ((homologyFunctor (ModuleCat S) (.down ℕ) i).map)
    (mapRestrictionIso_hom_naturality G f)
  simp only [CategoryTheory.Functor.map_comp] at hr
  have ht := toChainHomologyIso_hom_naturality ((G.mapHomologicalComplex _).map f)
    (fun j hj ↦ G.map_isZero (hK.isZero_X j hj))
    (fun j hj ↦ G.map_isZero (hL.isZero_X j hj)) i
  simp only [leftDerivedIsoCochain, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (toChainHomologyIso _ _ i).hom]
  erw [hr]
  simp only [Category.assoc]
  erw [ht]

/-- 関手と添字制限の比較は、関手の間の自然変換とも可換である。 -/
@[reassoc]
lemma mapRestrictionIso_natTrans (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} S)
    [F.Additive] [G.Additive] (α : F ⟶ G) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (NatTrans.mapHomologicalComplex α _).app (toChain K) ≫ (mapRestrictionIso G K).hom =
      (mapRestrictionIso F K).hom ≫
        restrictionMap ((NatTrans.mapHomologicalComplex α _).app K) embUp := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [mapRestrictionIso]
  rfl

/-- コチェイン分解による計算は、加法関手の間の自然変換と可換である。 -/
@[reassoc]
lemma leftDerivedIsoCochain_natTrans
    (F G : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive] [G.Additive] (α : F ⟶ G)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {X : ModuleCat.{u} R}
    (hK : IsResolutionOf K X) (i : ℕ) :
    (NatTrans.leftDerived α i).app X ≫ (leftDerivedIsoCochain G hK i).hom =
      (leftDerivedIsoCochain F hK i).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α _).app K) (-(i : ℤ)) := by
  have hn := hK.toProjectiveResolution.leftDerived_app_eq α i
  have hr := congrArg ((homologyFunctor (ModuleCat S) (.down ℕ) i).map)
    (mapRestrictionIso_natTrans F G α K)
  simp only [CategoryTheory.Functor.map_comp] at hr
  have ht := toChainHomologyIso_hom_naturality ((NatTrans.mapHomologicalComplex α _).app K)
    (fun j hj ↦ F.map_isZero (hK.isZero_X j hj))
    (fun j hj ↦ G.map_isZero (hK.isZero_X j hj)) i
  simp only [leftDerivedIsoCochain, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc _ _ (toChainHomologyIso _ _ i).hom]
  erw [hr]
  simp only [Category.assoc]
  erw [ht]

end SerrePositivity

end ResolutionNaturalityPart

section ResolutionMappingConePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{u} R}
namespace IsResolutionOf
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
variable (hK : IsResolutionOf K M₁) (hL : IsResolutionOf L M₂)
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (l : K ⟶ L)
  (hl : homologyMap l 0 = hK.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
    hL.homologyZeroIso.inv)

/-- Zero homology of a lifted cone is the cokernel module. -/
def coneHomologyZeroEquiv (hg : Function.Surjective g) (he : Function.Exact f g) :
    (CochainComplex.mappingCone l).homology 0 ≃ₗ[R] M₃ := by
  have h₂ := Cone.exact₂ l 0
  have h₃ := Cone.exact₃ l 0 1 rfl
  have hepi : Epi (homologyMap (CochainComplex.mappingCone.inr l) 0) :=
    h₃.epi_f ((hK.isZero_homology 1 one_ne_zero).eq_zero_of_tgt _)
  have hsurj := (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (homologyMap l 0).hom =
      LinearMap.ker (homologyMap (CochainComplex.mappingCone.inr l) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h₂
  let e₁ := hK.homologyZeroIso.toLinearEquiv
  let e₂ := hL.homologyZeroIso.toLinearEquiv
  have hmap : (LinearMap.range (homologyMap l 0).hom).map e₂.toLinearMap = LinearMap.range f := by
    rw [← LinearMap.range_comp, hl]
    have hc : e₂.toLinearMap.comp
        (hK.homologyZeroIso.hom ≫ ModuleCat.ofHom f ≫
          hL.homologyZeroIso.inv).hom = f.comp e₁.toLinearMap := by
      ext x
      simp [e₁, e₂]
    rw [hc, LinearMap.range_comp_of_range_eq_top _ e₁.range]
  exact (LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans
      ((Submodule.Quotient.equiv _ _ e₂ hmap).trans
        ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp he).symm).trans
          (LinearMap.quotKerEquivOfSurjective g hg))))

/-- The cone of a lift of an injective map resolves its cokernel module. -/
def mappingCone (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : Function.Exact f g) : IsResolutionOf (CochainComplex.mappingCone l) M₃ :=
    { isZero_X := fun i hi => by
        rw [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨hK.isZero_X _ (by omega), hL.isZero_X _ hi⟩
      projective := fun i => by
        have := hK.projective (i + 1)
        have := hL.projective i
        exact Projective.of_iso
          (HomologicalComplex.homotopyCofiber.XIsoBiprod l i (i + 1) rfl).symm inferInstance
      isZero_homology := fun i hi => by
        by_cases hi' : i = -1
        · subst i
          have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
          have h₃ := Cone.exact₃ l (-1) 0 h10
          have hz := hL.isZero_homology (-1) (by norm_num)
          have hmonoδ : Mono (Cone.δ l (-1) 0 h10) := h₃.mono_g (hz.eq_zero_of_src _)
          have hcomp : Cone.δ l (-1) 0 h10 ≫ homologyMap l 0 = 0 :=
            comp_eq_zero_transport (Cone.S₁ l (-1) 0 h10) _ _ _ _ _
              (Cone.δ_square l (-1) 0 h10) (Cone.e_naturality 0 l)
          have : Mono (homologyMap l 0) := by
            rw [hl]
            have : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
            infer_instance
          have hδ : Cone.δ l (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
          rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ l (-1) 0 h10),
            Category.id_comp, zero_comp, hδ]
        · exact (Cone.exact₃ l i (i + 1) rfl).isZero_of_both_isZero
            (hL.isZero_homology i hi) (hK.isZero_homology _ (by omega))
      homologyZeroIso := (hK.coneHomologyZeroEquiv hL f g l hl hg he).toModuleIso }

end IsResolutionOf
end SerrePositivity

end ResolutionMappingConePart

section ConeResolutionPart

open CategoryTheory Limits

namespace SerrePositivity

variable (A : Type u) [CommRing A]

/-- `A` 加群 `V` の射影分解（Mathlib の `projectiveResolution` で選んだもの）を ℤ 添字 cochain 複体に
延長したもの。`-n` 次の項が分解の `n` 番目の射影加群で、正の次数は零。 -/
noncomputable abbrev resV (V : Type u) [AddCommGroup V] [Module A V] :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  extRes (projectiveResolution (ModuleCat.of A V))

/-- `resV V` の `0` 次ホモロジーと `V` の同型（`extResHomologyZeroIso`）。長完全列の `0` 次の部分を
`V` の言葉に書き直すのに使う。 -/
noncomputable abbrev resVHomologyZeroIso (V : Type u) [AddCommGroup V] [Module A V] :
    (resV A V).homology 0 ≅ ModuleCat.of A V :=
  extResHomologyZeroIso (projectiveResolution (ModuleCat.of A V))

variable {A}
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]

/-- 線形写像 `f : V₁ → V₂` の、分解の間の鎖写像 `f̃ : resV V₁ ⟶ resV V₂` への持ち上げ（`extLift`）。
`0` 次のホモロジーで `f` を誘導する。この写像錐が `V₃` の分解になる。 -/
noncomputable abbrev liftSES (f : V₁ →ₗ[A] V₂) : resV A V₁ ⟶ resV A V₂ :=
  extLift (projectiveResolution (ModuleCat.of A V₁)) (ModuleCat.ofHom f)
    (projectiveResolution (ModuleCat.of A V₂))

/-- 持ち上げ `f̃` が `0` 次ホモロジーに誘導する射は、同一視 `resVHomologyZeroIso` のもとで `f` そのもの
である。`extLift_homologyZero` を同型で移項した形。 -/
lemma homologyMap_liftSES_zero (f : V₁ →ₗ[A] V₂) :
    HomologicalComplex.homologyMap (liftSES f) 0 =
      (resVHomologyZeroIso A V₁).hom ≫ ModuleCat.ofHom f ≫ (resVHomologyZeroIso A V₂).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact extLift_homologyZero _ _ _

variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃)

/-- 短完全列 `0 → V₁ →f V₂ →g V₃ → 0` について、`H^0(Cone f̃) ≃ V₃`。長完全列
`H^0(resV V₁) → H^0(resV V₂) → H^0(Cone f̃) → H^1(resV V₁) = 0` から、`H^0(Cone f̃)` は `H^0(f̃)` の
余核である。`H^0(f̃)` は同一視のもとで `f` なので余核は `V₂ / im f`、完全性 `im f = ker g` と `g` の
全射性から `V₂ / ker g ≅ V₃`。これらの同型を順につないで構成する。 -/
noncomputable def coneHomologyZeroEquiv (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    (Cone.cone (liftSES f)).homology 0 ≃ₗ[A] V₃ :=
  (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))).coneHomologyZeroEquiv
    (M₃ := ModuleCat.of A V₃)
    (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₂)))
    f g (liftSES f) (homologyMap_liftSES_zero f) hg hfg

/-- **持ち上げの錐は余核の分解**：短完全列 `0 → V₁ →f V₂ →g V₃ → 0` について、`Cone f̃` は `V₃` の
分解である。正の次数で零であることと射影性は項が直和であることから、ホモロジーの消滅は写像錐の
長完全列から（`i = -1` では `H^0(f̃)` の単射性を使って連結射が零になる）、`H^0 ≅ V₃` は
`coneHomologyZeroEquiv` による。 -/
noncomputable def isResolutionOf_cone (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    IsResolutionOf (Cone.cone (liftSES f)) (ModuleCat.of A V₃) :=
  (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))).mappingCone
    (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₂)))
    f g (liftSES f) (homologyMap_liftSES_zero f) hf hg hfg

end SerrePositivity

end ConeResolutionPart

section BoundedResolutionDimensionPart

namespace SerrePositivity
open CategoryTheory Limits Abelian
variable {R : Type u} [CommRing R]

/-- A bounded projective resolution supplies the categorical finite-projective-dimension bound. -/
lemma exists_projectiveDimensionLE_of_boundedResolution {M : ModuleCat.{u} R}
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F M)
    (hb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) :
    ∃ n, HasProjectiveDimensionLE M n := by
  obtain ⟨a, b, hb⟩ := hb
  let n := (-a).toNat
  let P := hF.toProjectiveResolution
  refine ⟨n, HasProjectiveDimensionLT.mk ?_⟩
  intro i hi Y e
  have hz : IsZero (P.complex.X i) := by
    have ht : IsZero (F.X (embUp.f i)) := hb _ (Or.inl (by
      simp only [embUp, ComplexShape.embeddingUpIntLE_f]
      dsimp [n] at hi
      omega))
    exact ht.of_iso (F.restrictionXIso embUp rfl).symm
  obtain ⟨f, hf, he⟩ := P.extMk_surjective e (i + 1) rfl
  have hf0 : f = 0 := hz.eq_zero_of_src f
  rw [← he]
  simp only [hf0, ProjectiveResolution.extMk_zero]

end SerrePositivity

end BoundedResolutionDimensionPart
