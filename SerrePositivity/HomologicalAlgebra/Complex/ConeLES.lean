module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # 写像錐のホモロジー長完全列と非輪状性

## 概要

複体の射 φ : K ⟶ L について、写像錐を含む長完全列 … → H^n(K) → H^n(L) → H^n(Cone φ) → H^{n+1}(K) → … を三つの短複体の完全性 `exact₂`・`exact₃`・`exact₁` として取り出す。非輪状性は同型・ホモトピー同値・シフトで保たれ、φ が擬同型であることと写像錐が非輪状であることは同値である（`cochain_quasiIso_iff_cone_acyclic`）。

## 方針

ホモトピー圏の完全三角形とホモロジー関手の完全性から長完全列を読む。

## 規約

importer が多い（16 本）ので軽く保つ。`QuasiIso f ↔ (mappingCone f).Acyclic` はアーベル圏へ一般化して Mathlib へ提出する候補。

## 使われ方

Koszul ホモロジー、Tor の長完全列、PerfectComplex の擬同型の判定。
-/

@[expose] public noncomputable section

universe u

section ConeLESPart

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 短複体の移送 -/

/-- 短複体 `S`（`S.f ≫ S.g = 0`）の三つの対象をそれぞれ同型 `e₁`、`e₂`、`e₃` で置き換え、射 `f`、`g`
が `S.f`、`S.g` と同型を通して対応している（`h₁`、`h₂`）なら、`f ≫ g = 0` である。
`f = e₁⁻¹ ≫ S.f ≫ e₂`、`g = e₂⁻¹ ≫ S.g ≫ e₃` と書き直せば `S.f ≫ S.g = 0` に帰着する。
`exact_transport` で移した短複体を `ShortComplex.mk` で作るときの、零合成の証明として使う。 -/
lemma comp_eq_zero_transport (S : ShortComplex (ModuleCat.{u} R))
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) : f ≫ g = 0 := by
  have hf : f = e₁.inv ≫ S.f ≫ e₂.hom := by rw [h₁, Iso.inv_hom_id_assoc]
  have hg : g = e₂.inv ≫ S.g ≫ e₃.hom := by rw [h₂, Iso.inv_hom_id_assoc]
  rw [hf, hg, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc,
    zero_comp, comp_zero]

/-- 短複体 `S` が完全なら、三つの対象を同型 `e₁`、`e₂`、`e₃` で置き換え、対応する射 `f`、`g` で
作った短複体も完全である。同型 `e` から短複体の同型 `ShortComplex.isoMk` を作り、Mathlib の
`ShortComplex.exact_of_iso` を適用する。このファイルでは三角圏側で得た完全性を複体のホモロジー
側に移すのに使い、`TorLES.lean` では複体側の完全性をさらに Tor の側に移すのに使う。 -/
lemma exact_transport {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) :
    (ShortComplex.mk f g (comp_eq_zero_transport S e₁ e₂ e₃ f g h₁ h₂)).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm) hS

namespace Cone

/-! ## ホモトピー圏のホモロジー関手 -/

/-- ホモトピー圏 `K(R)` 上の 0 次ホモロジー関手。三角圏の homological functor として扱い、`n` 次の
ホモロジーは shift との合成として得る。Mathlib の `homologySequence` の API は一つの homological
functor を shift して使う形で書かれているので、それに合わせて 0 次のものに名前を付けておく。 -/
noncomputable abbrev H₀ :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤ ModuleCat.{u} R :=
  HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0

/-- ホモトピー圏の `n` 次ホモロジー関手を複体 `L` の類に施したものと、複体のホモロジー
`L.homology n` を結ぶ同型。Mathlib の自然同型 `homologyFunctorFactors`（「ホモロジー関手は商関手を
経由する」）の `L` 成分である。三角圏側で得た完全列を複体の言葉に移すときの橋渡しになる。 -/
noncomputable abbrev e (n : ℤ) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj L) ≅ L.homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app L

/-- 同一視 `e` は複体の射 `f : L ⟶ L'` と両立する：ホモトピー圏側で `f` の類が誘導する射を
`e n L'` と合成したものは、`e n L` を複体側のホモロジー射 `homologyMap f n` と合成したものに
等しい。`homologyFunctorFactors` の自然性そのもの。`exact_transport` に渡す可換性の仮定として、
三角形の射 `φ` と `inr φ` について使う。 -/
lemma e_naturality (n : ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ L') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map f) ≫ (e n L').hom =
      (e n L).hom ≫ HomologicalComplex.homologyMap f n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).hom.naturality f

/-! ## 写像錐の長完全列 -/

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- 複体の射 `φ : K ⟶ L` の写像錐 `Cone φ`。Mathlib の `CochainComplex.mappingCone φ` の別名で、
長完全列に現れる第三の複体である。`i` 次の項は `K^{i+1} ⊕ L^i` で、`L` は `inr φ` で埋め込まれ、
`K[1]` が商として現れる。 -/
noncomputable abbrev cone : CochainComplex (ModuleCat.{u} R) ℤ := CochainComplex.mappingCone φ

/-- 写像錐の三角形 `K → L → Cone φ → K[1]` は、ホモトピー圏の完全三角形（distinguished triangle）
である。Mathlib の `mappingCone_triangleh_distinguished` の言い換えで、homological functor の
長完全列を適用するための前提になる。 -/
lemma triangleh_distinguished :
    CochainComplex.mappingCone.triangleh φ ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished _

/-- 連結射 `δ : H^{n₀}(Cone φ) → H^{n₁}(K)`（`n₁ = n₀ + 1`）。長完全列で `H^{n₀}(Cone φ)` から
一つ上の次数の `H^{n₀+1}(K)` へ戻る射である。三角圏側の連結射 `homologySequenceδ` を、両端で
同一視 `e` と合成して複体のホモロジーの間の射にしたもの。 -/
noncomputable def δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : (cone φ).homology n₀ ⟶ K.homology n₁ :=
  (e n₀ (cone φ)).inv ≫
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
    (e n₁ K).hom

/-- `δ` の定義を可換図式の形で述べたもの：三角圏側の連結射のあとに `e n₁ K` を合成したものは、
`e n₀ (Cone φ)` のあとに `δ` を合成したものに等しい。定義を展開して `e.hom ≫ e.inv = 𝟙` で
消すだけ。`exact_transport` に渡す可換性の仮定として使う。 -/
lemma δ_square (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
        (e n₁ K).hom =
      (e n₀ (cone φ)).hom ≫ δ φ n₀ n₁ h := by
  rw [δ, Iso.hom_inv_id_assoc]
  rfl

/-- 三角圏側の短複体 `H^n(K) → H^n(L) → H^n(Cone φ)`。射は、ホモロジー関手が三角形の射
`φ`、`inr φ` から誘導するもので、合成が零であることは homological functor の性質
（`homologySequence_comp`）から出る。 -/
noncomputable abbrev S₂ (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequence_comp _ (triangleh_distinguished φ) n)

/-- 三角圏側の短複体 `H^{n₀}(L) → H^{n₀}(Cone φ) → H^{n₁}(K)`（`n₁ = n₀ + 1`）。第二の射は三角圏側の
連結射で、合成が零であることは `comp_homologySequenceδ` による。 -/
noncomputable abbrev S₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((H₀ (R := R)).comp_homologySequenceδ _ (triangleh_distinguished φ) n₀ n₁ h)

/-- 三角圏側の短複体 `H^{n₀}(Cone φ) → H^{n₁}(K) → H^{n₁}(L)`（`n₁ = n₀ + 1`）。第一の射は三角圏側の
連結射で、合成が零であることは `homologySequenceδ_comp` による。 -/
noncomputable abbrev S₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((H₀ (R := R)).homologySequenceδ_comp _ (triangleh_distinguished φ) n₀ n₁ h)

/-- 長完全列の中央部分：`H^n(K) → H^n(L) → H^n(Cone φ)` は完全である。二つの射は `φ` と、
写像錐への埋め込み `inr φ : L ⟶ Cone φ` がホモロジーに誘導するもの。三角圏側の完全性
`homologySequence_exact₂` を同一視 `e` で複体側に移す。 -/
lemma exact₂ (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap φ n)
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n)
      (comp_eq_zero_transport (S₂ φ n) (e n K) (e n L) (e n (cone φ))
        _ _ (e_naturality n φ)
        (e_naturality n (CochainComplex.mappingCone.inr φ)))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₂ _ (triangleh_distinguished φ) n)
    (e n K) (e n L) (e n (cone φ)) _ _ (e_naturality n φ)
    (e_naturality n (CochainComplex.mappingCone.inr φ))

/-- 長完全列の右側：`H^{n₀}(L) → H^{n₀}(Cone φ) → H^{n₁}(K)`（`n₁ = n₀ + 1`）は完全である。
第一の射は `inr φ` がホモロジーに誘導するもの、第二の射は連結射 `δ`。三角圏側の完全性
`homologySequence_exact₃` を `e` で移す。 -/
lemma exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n₀)
      (δ φ n₀ n₁ h)
      (comp_eq_zero_transport (S₃ φ n₀ n₁ h) (e n₀ L) (e n₀ (cone φ))
        (e n₁ K) _ (δ φ n₀ n₁ h)
        (e_naturality n₀ (CochainComplex.mappingCone.inr φ))
        (δ_square φ n₀ n₁ h))).Exact :=
  exact_transport
    ((H₀ (R := R)).homologySequence_exact₃ _ (triangleh_distinguished φ) n₀ n₁ h)
    (e n₀ L) (e n₀ (cone φ)) (e n₁ K) _ (δ φ n₀ n₁ h)
    (e_naturality n₀ (CochainComplex.mappingCone.inr φ)) (δ_square φ n₀ n₁ h)

/-- 長完全列の左側：`H^{n₀}(Cone φ) → H^{n₁}(K) → H^{n₁}(L)`（`n₁ = n₀ + 1`）は完全である。
第一の射は連結射 `δ`、第二の射は `φ` がホモロジーに誘導するもの。三角圏側の完全性
`homologySequence_exact₁` を `e` で移す。 -/
lemma exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (δ φ n₀ n₁ h) (HomologicalComplex.homologyMap φ n₁)
      (comp_eq_zero_transport (S₁ φ n₀ n₁ h) (e n₀ (cone φ)) (e n₁ K)
        (e n₁ L) (δ φ n₀ n₁ h) _ (δ_square φ n₀ n₁ h)
        (e_naturality n₁ φ))).Exact :=
  exact_transport
    ((H₀ (R := R)).homologySequence_exact₁ _ (triangleh_distinguished φ) n₀ n₁ h)
    (e n₀ (cone φ)) (e n₁ K) (e n₁ L) (δ φ n₀ n₁ h) _
    (δ_square φ n₀ n₁ h) (e_naturality n₁ φ)

end Cone

end SerrePositivity

end ConeLESPart

section CochainAcyclicPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]

lemma cochainAcyclic_of_iso {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (e : P ≅ Q) : Q.Acyclic :=
  fun i => (hP i).of_iso e

lemma cochainAcyclic_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (e : HomotopyEquiv P Q) : Q.Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology Q i).mpr
    ((e.toHomologyIso i).isZero_iff.mp (hP i).isZero_homology)

lemma cochainAcyclic_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (n : ℤ) : (P⟦n⟧).Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    (((CochainComplex.ShiftSequence.shiftIso
      (ModuleCat.{u} R) n i (n + i) rfl).app P).isZero_iff.mpr
      (hP (n + i)).isZero_homology)

lemma cochainAcyclic_of_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (n : ℤ) (hP : (P⟦n⟧).Acyclic) : P.Acyclic :=
  cochainAcyclic_of_iso (cochainAcyclic_shift hP (-n)) (shiftShiftNeg P n)

lemma cochainAcyclic_mappingCone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : P.Acyclic) (hQ : Q.Acyclic) : (mappingCone f).Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    ((Cone.exact₃ f i (i + 1) rfl).isZero_of_both_isZero
      (hQ i).isZero_homology (hP (i + 1)).isZero_homology)

/-- A cochain map is a quasi-isomorphism precisely when its concrete cone is acyclic. -/
lemma cochain_quasiIso_iff_cone_acyclic
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

end SerrePositivity

end CochainAcyclicPart
