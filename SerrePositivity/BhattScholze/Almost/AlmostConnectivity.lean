module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.SurjectiveQuotientPerfectoidization
public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.Homology
public import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor

/-! # 商の perfectoid 化の核と複体の almost 零性

## 概要
BS 著者版 Proposition 10.4 と Lemma 10.5 の核とコホモロジーの条件を定める。
根基不変性と、離散加群に対する完備テンソルの消滅を示す。

## 方針
古典的な商の perfectoid 化の普遍性と、一般の perfectoid 商に対する Lemma 10.3 を使う。

## 規約
次数はコホモロジー次数。J-almost 零性は各コホモロジー加群の零化条件。

## 使われ方
BS 著者版 Proposition 10.4 の複体版。
-/

@[expose] public noncomputable section
universe u
open SerrePositivity
namespace SerrePositivity.BhattScholze.Almost

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
  (J : Ideal R)

/-- 古典的な商の perfectoid 化への標準射（BS 著者版 Theorem 7.4）。 -/
def quotientPerfdMap : R →+* QuotientPerfectoidization R J p hR :=
  (toQuotientPerfectoidization R J p hR).comp (Ideal.Quotient.mk J)

/-- BS 著者版 Definition 10.1 の perfectoid 化の核。 -/
def perfectoidKernel : Ideal R := RingHom.ker (quotientPerfdMap p R hR J)

/-- 元のイデアルは perfectoid 化の核に含まれる。 -/
theorem le_perfectoidKernel : J ≤ perfectoidKernel p R hR J := by
  intro x hx
  rw [perfectoidKernel, RingHom.mem_ker, quotientPerfdMap, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- 元のイデアルを殺す perfectoid 環への写像は、この核も殺す。 -/
theorem perfectoidKernel_le {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (f : R →+* T) (h : J ≤ RingHom.ker f) :
    perfectoidKernel p R hR J ≤ RingHom.ker f := by
  let f' := Ideal.Quotient.lift J f (fun x hx => h hx)
  obtain ⟨l, hl, _⟩ := (isPerfectoidization_toQuotientPerfectoidization R J p hR).2 T hT f'
  intro x hx
  change quotientPerfdMap p R hR J x = 0 at hx
  change f x = 0
  have he := DFunLike.congr_fun hl (Ideal.Quotient.mk J x)
  change l (quotientPerfdMap p R hR J x) = f x at he
  rw [hx, map_zero] at he
  exact he.symm

/-- perfectoid 化の核は元のイデアルについて単調。 -/
theorem perfectoidKernel_mono {I : Ideal R} (h : J ≤ I) :
    perfectoidKernel p R hR J ≤ perfectoidKernel p R hR I :=
  perfectoidKernel_le p R hR J (isPerfectoidization_toQuotientPerfectoidization R I p hR).1
    (quotientPerfdMap p R hR I) (h.trans (le_perfectoidKernel p R hR I))

/-- perfectoid 環の被約性により、核は元のイデアルの根基で決まる。 -/
theorem perfectoidIdeal_radical :
    perfectoidKernel p R hR J = perfectoidKernel p R hR J.radical := by
  refine le_antisymm (perfectoidKernel_mono p R hR J Ideal.le_radical) ?_
  have hB := (isPerfectoidization_toQuotientPerfectoidization R J p hR).1
  have := hB.isReduced _ p
  refine perfectoidKernel_le p R hR J.radical hB (quotientPerfdMap p R hR J) ?_
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  have hh := le_perfectoidKernel p R hR J hn
  change quotientPerfdMap p R hR J (x ^ n) = 0 at hh
  rw [map_pow] at hh
  exact IsNilpotent.eq_zero ⟨n, hh⟩

open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
open SerrePositivity.InfinityCategories SSet
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

/-- 全次数のコホモロジーが J-almost 零である（BS 著者版 Proposition 10.4）。 -/
def IsJAlmostZero (M : DVertex R) : Prop :=
  ∀ i : ℤ, SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R i M)

/-- 正次数のコホモロジーが J-almost 零である（BS 著者版 Lemma 10.5）。 -/
def IsAlmostConnective (M : DVertex R) : Prop :=
  ∀ i : ℤ, 0 < i → SerrePositivity.Almost.IsAlmostZero (perfectoidKernel p R hR J)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology R i M)

/-- 複体の J-almost 零性は根基で決まる。 -/
theorem isAlmostZero_radical (M : DVertex R) :
    IsJAlmostZero p R hR J M ↔ IsJAlmostZero p R hR J.radical M := by
  rw [IsJAlmostZero, IsJAlmostZero, ← perfectoidIdeal_radical p R hR J]
/-- 古典的な商への写像に対する BS 著者版 Theorem 7.4 の全射性。 -/
theorem quotientPerfdMap_surjective : Function.Surjective (quotientPerfdMap p R hR J) := by
  have hs := surjective_perfectoidization_of_quotient p hR
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    (toQuotientPerfectoidization R J p hR)
    (isPerfectoidization_toQuotientPerfectoidization R J p hR)
  exact hs.comp Ideal.Quotient.mk_surjective

/-- 核で割った商は古典的な perfectoid 化と環同型なので perfectoid。 -/
theorem perfectoidKernel_quotient_isIntegralPerfectoid :
    IsIntegralPerfectoid (R ⧸ perfectoidKernel p R hR J) p :=
  isIntegralPerfectoid_of_ringEquiv p
    (RingHom.quotientKerEquivOfSurjective (quotientPerfdMap_surjective p R hR J)).symm
    (isPerfectoidization_toQuotientPerfectoidization R J p hR).1

/-- BS 著者版 Proposition 10.4 の順方向を、任意の J と離散加群について示す。 -/
theorem perfectoidKernel_completedTensor_isZero_of_isAlmostZero
    (M : ModuleCat.{u} R) (hM : SerrePositivity.Almost.IsAlmostZero
      (perfectoidKernel p R hR J) M) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (perfectoidKernel p R hR J))).obj M)) := by
  let K := perfectoidKernel p R hR J
  let := SerrePositivity.Almost.quotientModule K M hM
  let := SerrePositivity.Almost.quotientModule_scalarTower K M hM
  exact completedTensor_isZero_of_algebraModule R (p : R) (R ⧸ K) M
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R K))
    (integralPerfectoid_completedIdealTensorQuotient_isZero p K hR
      (perfectoidKernel_quotient_isIntegralPerfectoid p R hR J))

end SerrePositivity.BhattScholze.Almost


namespace SerrePositivity.BhattScholze.Perfectoidization.Derived
open CategoryTheory InfinityCategories DerivedCompletion
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

/-- 頂点を通常の導来圏に移し、主元 p に関する導来完備性を判定する。 -/
def isPCompleteVertex (p : ℕ) (R : Type u) [CommRing R]
    (M : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌) : Prop :=
  IsComplete R (p : R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨M⟩)

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 10.1"] _root_.SerrePositivity.BhattScholze.Almost.IsJAlmostZero
attribute [cite BS19 "Def 10.1"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidKernel
attribute [cite BS19 "Lemma 10.3" (partial := special) "三主張とも本体（sorry 0）。名前つきの宣言は単項 J=(g) の核だが、一般形 integralPerfectoid_* と perfectoidKernel_quotient_isIntegralPerfectoid を組めば任意の J で成り立つ（特殊化の宣言はない、11-12 節の見直し）。一般の perfectoid 商 R→R/K に対する混合積消滅・自己積（integralPerfectoid_*）は一般形。DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：lemma103_perfectoidTensor（商の自己積の同型を示す証明に利用するが、この型は積射の同型を主張しない。） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidKernel_quotient_isIntegralPerfectoid
