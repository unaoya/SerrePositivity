module

import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationRawBasis
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationRawRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulCompletionRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComparison

/-!
# 有限根関係の完備化後の正則性と通常商

## 概要
完備な根付き基底の Xi−fi は Koszul 正則で、その通常商は既に導来 p 完備。
生の商の実完備化との比較を、指定した単位を保つ環同型として得る。
## 方針
生の関係商の自由基底と各項完備化の比較を使う。
## 規約
BS 著者版 Proposition 7.10。完備化を定義で同一視せず比較として示す。
## 使われ方
有限 T の有界ねじれと有界な prismatic envelope。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Andre
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)
local notation "Raw" => rootFamilyRaw p R (Fin r)
local notation "Base" => rootFamilyBase p R (Fin r)

/-- 完備な根付き基底上の有限初期関係の列。 -/
def rootRelationSequence : Fin r → Base :=
  rootFamilyUnit p R (Fin r) ∘ rootFamilyPolynomialMap p R (Fin r) ∘ rootRelationPolynomial R f

/-- 生の根関係のイデアルは像の関係列で生成される。 -/
theorem rootRelationRawIdeal_eq : rootRelationRawIdeal p R f =
    Ideal.span (Set.range (rootFamilyPolynomialMap p R (Fin r) ∘ rootRelationPolynomial R f)) := by
  rw [rootRelationRawIdeal, rootRelationPolynomialIdeal, Ideal.map_span, ← Set.range_comp]

/-- 生の関係イデアルを実完備化へ送ったイデアル。 -/
def rootRelationBaseIdeal : Ideal Base :=
  (rootRelationRawIdeal p R f).map (rootFamilyUnit p R (Fin r))

/-- 完備な基底の通常の有限関係商。 -/
abbrev rootRelationQuotient := Base ⧸ rootRelationBaseIdeal p R f

/-- 生の関係商を実 H⁰ 完備化する模型。 -/
abbrev rootRelationRawCompleted := CompletedRing p (rootRelationRaw p R f)

/-- 完備化後のイデアルは、完備化した関係列で生成される。 -/
theorem rootRelationBaseIdeal_eq : rootRelationBaseIdeal p R f =
    Ideal.span (Set.range (rootRelationSequence p R f)) := by
  rw [rootRelationBaseIdeal, rootRelationRawIdeal_eq, Ideal.map_span, ← Set.range_comp]
  rfl

/-- 概要：完備な根付き基底の有限関係は Koszul 正則。
方針：生の環と商の係数環上の自由性を、各項完備化の定理へ渡す。
規約：BS 著者版 Proposition 7.10。係数の p 正則性は不要。
使われ方：有限 T の表示に対する Example 7.9。 -/
theorem rootRelationSequence_isKoszulResolution : IsKoszulResolution (rootRelationSequence p R f) := by
  letI : Module.Free R Raw := Module.Free.of_basis (AddMonoidAlgebra.basis _ _)
  let z := rootFamilyPolynomialMap p R (Fin r) ∘ rootRelationPolynomial R f
  letI : Module.Free R (Raw ⧸ Ideal.span (Set.range z)) := by
    rw [← rootRelationRawIdeal_eq]
    exact rootRelationRaw_free p R f
  have h := completedKoszul_isKoszulResolution R Raw p z (rootRelationRaw_isKoszulResolution p R f)
  exact h

/-- 通常の有限関係商は既に導来 p 完備である。 -/
theorem rootRelationQuotient_complete :
    IsModuleComplete (rootRelationQuotient p R f) (p : rootRelationQuotient p R f)
      (ModuleCat.of (rootRelationQuotient p R f) (rootRelationQuotient p R f)) := by
  have hBase : IsModuleComplete Base (p : Base) (ModuleCat.of Base Base) :=
    principalCompletionRing_self_complete Raw p
  have h := isModuleComplete_finiteRelationQuotient Base (p : Base) hBase (rootRelationSequence p R f)
  rw [← rootRelationBaseIdeal_eq] at h
  have h' := (isModuleComplete_algebraMap_iff Base (rootRelationQuotient p R f) (p : Base)
    (rootRelationQuotient p R f)).mpr h
  simpa only [map_natCast] using h' 

/-- 概要：完備な基底の通常商と、生の有限関係商の実完備化は単位を保って同型。
方針：通常商の導来完備性を、既存の環の普遍性の比較へ渡す。
規約：BS 著者版 Proposition 7.10。drafts の定義は変更しない。
使われ方：有限 T の有界ねじれを生の商から移す。 -/
theorem exists_rootRelationQuotient_rawCompleted_equiv :
    ∃ e : rootRelationQuotient p R f ≃+* rootRelationRawCompleted p R f,
      e.toRingHom.comp
        (Ideal.quotientMap (rootRelationBaseIdeal p R f) (rootFamilyUnit p R (Fin r)) Ideal.le_comap_map) =
        (principalCompletionRingCatUnit p (CommRingCat.of (rootRelationRaw p R f))).hom :=
  exists_principalCompletionQuotientEquiv_of_complete Raw p (rootRelationRawIdeal p R f)
    (rootRelationQuotient_complete p R f)

end SerrePositivity.BhattScholze.Semiperfectoid
