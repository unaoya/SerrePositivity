module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
public import Mathlib.RingTheory.FinitePresentation
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs

/-! # perfectoid イデアル

## 概要

integral perfectoid な `R` と `g : R` に対し、主イデアル商 `R/(g)` の perfectoid 化（BS の B3 で選んだ普遍対象）への写像の核として perfectoid イデアル `perfectoidIdeal` を定める。`(g) ⊆ perfectoidIdeal`、`g` が単元なら全体、単調性を示す。環準同型に沿った主イデアル商の perfectoid 化の射（`quotientPerfectoidizationMap`）とその合成、perfectoid イデアルの像の包含と商の間の写像を与える。
BS 著者版 §10.1 の単項 J に対する J_perfd を定め、Definition 10.1 の零化条件に使う。

## 方針

射は perfectoid 化の普遍性（CommutativeAlgebra/Perfectoid/Defs）だけから作る。整代数の perfectoid 化の存在の引用は使わない。

## 規約

平坦性や perfectoid 化の基底変更の同型は主張しない。名前 `perfectoidIdeal` は CLMST・監査が使うので変えない。旧 `CommutativeAlgebra/PerfectoidIdeal`・`PerfectoidizationMap`・`PerfectoidIdealFunctor`（2a で BS の下へ移した）。

## 使われ方

`PerfectoidIdeal/Powers`・`Cover`、BS の Almost・Perfectoidization/Excision、CLMST。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIdealPart

namespace SerrePositivity

/-- CLMSTの(g)_perfd（BS 著者版 §10.1 の導入で定める J_perfd の単項 J の場合、序論の Remark 1.13）。
  B3の標準写像との合成の核で定義する。 -/
def perfectoidIdeal (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R) : Ideal R :=
  RingHom.ker ((toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g})))

end SerrePositivity

end PerfectoidIdealPart

section PerfectoidizationMapPart

namespace SerrePositivity

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- 元の主イデアルは、その perfectoid イデアルに含まれる。 -/
theorem span_le_perfectoidIdeal (g : R) : Ideal.span {g} ≤ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  apply Ideal.span_le.mpr
  intro x hx
  have hxg : x = g := Set.mem_singleton_iff.mp hx
  subst x
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) g) = 0
  have hz : Ideal.Quotient.mk (Ideal.span {g}) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton g))
  rw [hz, map_zero]

/-- 単元のperfectoidイデアルは全体。全射性や商の被約性は必要ない。 -/
theorem perfectoidIdeal_eq_top_of_isUnit (g : R) (hg : IsUnit g) :
    perfectoidIdeal R p hR g = ⊤ := by
  apply top_unique
  have hh := span_le_perfectoidIdeal R p hR g
  rwa [Ideal.span_singleton_eq_top.mpr hg] at hh

/-- 主イデアルの包含は perfectoid イデアルの包含を与える。
商環間の写像を普遍性で perfectoid 化へ移し、核の包含を証明する。 -/
theorem perfectoidIdeal_mono {g k : R} (h : Ideal.span {g} ≤ Ideal.span {k}) :
    perfectoidIdeal R p hR g ≤ perfectoidIdeal R p hR k := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {k}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton k)
  let q : R ⧸ Ideal.span {g} →+* R ⧸ Ideal.span {k} := Ideal.Quotient.factor h
  let hg := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  let hk := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {k}) p hR
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) x) = 0 at hx
  change toQuotientPerfectoidization R (Ideal.span {k}) p hR
    (Ideal.Quotient.mk (Ideal.span {k}) x) = 0
  have he := RingHom.congr_fun (IsPerfectoidization.map_comp hg hk q)
    (Ideal.Quotient.mk (Ideal.span {g}) x)
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact he.symm

end SerrePositivity

end PerfectoidizationMapPart

section PerfectoidIdealFunctorPart

namespace SerrePositivity
variable {R S : Type u} [CommRing R] [CommRing S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hS : IsIntegralPerfectoid S p) (φ : R →+* S)

/-- The induced map of the original chosen quotient perfectoidizations. -/
def quotientPerfectoidizationMap (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap φ) :
    QuotientPerfectoidization R I p hR →+* QuotientPerfectoidization S J p hS :=
  IsPerfectoidization.map (isPerfectoidization_toQuotientPerfectoidization R I p hR)
    (isPerfectoidization_toQuotientPerfectoidization S J p hS)
    (Ideal.quotientMap J φ hIJ)

/-- The induced map commutes with the original quotient perfectoidization units. -/
theorem quotientPerfectoidizationMap_comp (I : Ideal R) (J : Ideal S)
    (hIJ : I ≤ J.comap φ) :
    (quotientPerfectoidizationMap p hR hS φ I J hIJ).comp
      (toQuotientPerfectoidization R I p hR) =
    (toQuotientPerfectoidization S J p hS).comp (Ideal.quotientMap J φ hIJ) :=
  IsPerfectoidization.map_comp _ _ _

/-- In particular the base-ring representatives retain their original images. -/
@[simp] theorem quotientPerfectoidizationMap_mk (I : Ideal R) (J : Ideal S)
    (hIJ : I ≤ J.comap φ) (x : R) :
    quotientPerfectoidizationMap p hR hS φ I J hIJ
      (toQuotientPerfectoidization R I p hR (Ideal.Quotient.mk I x)) =
      toQuotientPerfectoidization S J p hS (Ideal.Quotient.mk J (φ x)) := by
  exact RingHom.congr_fun (quotientPerfectoidizationMap_comp p hR hS φ I J hIJ)
    (Ideal.Quotient.mk I x)

/-- The original perfectoid ideal maps into the ideal of the image generator. -/
theorem perfectoidIdeal_map_le (g : R) :
    (perfectoidIdeal R p hR g).map φ ≤ perfectoidIdeal S p hS (φ g) := by
  apply Ideal.map_le_iff_le_comap.mpr
  have hIJ : Ideal.span {g} ≤ (Ideal.span {φ g}).comap φ := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span (Set.mem_singleton _)
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk (Ideal.span {g}) x) = 0 at hx
  change toQuotientPerfectoidization S (Ideal.span {φ g}) p hS
    (Ideal.Quotient.mk (Ideal.span {φ g}) (φ x)) = 0
  have he := quotientPerfectoidizationMap_mk p hR hS φ
    (Ideal.span {g}) (Ideal.span {φ g}) hIJ x
  rw [hx, map_zero] at he
  exact he.symm

/-- Every original almost scalar remains an almost scalar after the base map. -/
theorem map_mem_perfectoidIdeal (g x : R) (hx : x ∈ perfectoidIdeal R p hR g) :
    φ x ∈ perfectoidIdeal S p hS (φ g) :=
  perfectoidIdeal_map_le p hR hS φ g (Ideal.mem_map_of_mem φ hx)

/-- The map on the actual kernel quotients uses precisely the original base map. -/
def perfectoidIdealQuotientMap (g : R) :
    R ⧸ perfectoidIdeal R p hR g →+* S ⧸ perfectoidIdeal S p hS (φ g) :=
  Ideal.quotientMap _ φ
    (Ideal.map_le_iff_le_comap.mp (perfectoidIdeal_map_le p hR hS φ g))

@[simp] theorem perfectoidIdealQuotientMap_mk (g x : R) :
    perfectoidIdealQuotientMap p hR hS φ g
      (Ideal.Quotient.mk (perfectoidIdeal R p hR g) x) =
      Ideal.Quotient.mk (perfectoidIdeal S p hS (φ g)) (φ x) := rfl

end SerrePositivity

end PerfectoidIdealFunctorPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 1.13" (partial := special) "§10.1・Prop 10.2 の言い直し。本体は主イデアル (g) の J_perfd と Prop 10.2 の一部。有限生成 J の J-almost 基本は drafts/A8/AlmostConnectivity ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：perfectoidIdeal_conormal_completion_isZero（序論が述べる核の自己テンソル同型から導く別の主張。Lemma 10.3 の応用として扱う。） ／ DOC1 照合：ok 1 件"] _root_.SerrePositivity.perfectoidIdeal
