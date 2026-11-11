module

public import SerrePositivity.HomologicalAlgebra.CochainFlatDetection
public import SerrePositivity.HomologicalAlgebra.CochainCompleteDetection

/-!
# 正則列の忠実平坦な剰余から完備底変換を検出する

## 概要
標的の正則主元による剰余が正則列の商から忠実平坦なら、完備底変換は零性を反映する。

## 方針
標的の完備化の Koszul 簡約、通常商への比較、忠実平坦性、有限 Koszul Nakayama をつなぐ。

## 規約
BS 著者版 Proposition 6.2 の一般の環・非有界な複体での入力。

## 使われ方
Construction 6.1 の式 (6) と (p,d) の正則列へ適用する。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex DifferentialGraded DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：正則主元のスカラー錐の零性は、K-flat 模型の通常剰余の零性と同値。
方針：一元 Koszul 分解の実際の比較射を用いる。
規約：BS 著者版 Proposition 6.2、非有界な入力。使われ方：標的の mod p への移行。 -/
theorem regularPrincipalBaseChange_homology_isZero_iff
    (a : R) (ha : IsSMulRegular R a) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : complexKFlat R K) (i : ℤ) :
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span {a})) K).homology i) ↔
      IsZero (((scalarConeFunctor a).obj K).homology i) := by
  let x : Fin 1 → R := fun _ => a
  have hx : IsKoszulResolution x := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn x = [a] by simp [x, List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr ha
  have he : Set.range x = {a} := by ext b; simp [x]
  let G (s : Set R) : Prop :=
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span s)) K).homology i) ↔
      IsZero (((scalarConeFunctor a).obj K).homology i)
  exact Eq.mp (congrArg G he)
    (show G (Set.range x) from regularQuotientBaseChange_homology_isZero_iff x hx K hK i)

/-- 概要：正則列の商を忠実平坦に覆う剰余の底変換は完備な入力の零性を反映する。
方針：係数拡大の合成、忠実平坦なホモロジー検出、Koszul 比較と Nakayama を使う。
規約：BS 著者版 Proposition 6.2。実際の K-flat 模型で、上の有界性を課さない。
使われ方：被覆の mod p の底変換から元の複体へ戻る。 -/
theorem cochain_acyclic_of_faithfullyFlat_regularQuotient
    (f : R →+* S) {r : ℕ} (x : Fin r → R) (hx : IsKoszulResolution x)
    (g : (R ⧸ Ideal.span (Set.range x)) →+* S) (hg : g.FaithfullyFlat)
    (hf : f = g.comp (Ideal.Quotient.mk (Ideal.span (Set.range x))))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : complexKFlat R K)
    (hc : ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj K))
    (h : ∀ i : ℤ, IsZero ((baseChange f K).homology i)) :
    ∀ i : ℤ, IsZero (K.homology i) := by
  apply cochain_acyclic_of_complete_of_koszul_acyclic x K hc
  intro i
  let q := Ideal.Quotient.mk (Ideal.span (Set.range x))
  have h₀ : IsZero ((baseChange (g.comp q) K).homology i) := by simpa only [hf] using h i
  have h₁ := h₀.of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso (baseChangeCompIso q g K))
  exact (regularQuotientBaseChange_homology_isZero_iff x hx K hK i).mp
    (cochain_homology_isZero_of_faithfullyFlat_baseChange g hg (baseChange q K) i h₁)

/-- 概要：標的主元の剰余に忠実平坦な正則列表示があれば、二回の完備底変換は零性を反映する。
方針：完備化から主元錐へ戻し、K-flat 模型で通常商と合成底変換を同定する。
規約：BS 著者版 Proposition 6.2、結晶被覆の二座標完備化の非有界な模型。
使われ方：Construction 6.1 の保存性。 -/
theorem cochain_acyclic_of_repeatedCompletedBaseChange_acyclic
    (f : R →+* S) (a : S) (ha : IsSMulRegular S a)
    {r : ℕ} (x : Fin r → R) (hx : IsKoszulResolution x)
    (g : (R ⧸ Ideal.span (Set.range x)) →+* (S ⧸ Ideal.span {a}))
    (hg : g.FaithfullyFlat)
    (hf : (Ideal.Quotient.mk (Ideal.span {a})).comp f =
      g.comp (Ideal.Quotient.mk (Ideal.span (Set.range x))))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : complexKFlat R K)
    (hS : complexKFlat S (baseChange f K))
    (hc : ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj K))
    (h : ∀ i : ℤ, IsZero (((complexCompletionFunctor S a).obj
      ((complexCompletionFunctor S a).obj (baseChange f K))).homology i)) :
    ∀ i : ℤ, IsZero (K.homology i) := by
  apply cochain_acyclic_of_faithfullyFlat_regularQuotient
    ((Ideal.Quotient.mk (Ideal.span {a})).comp f) x hx g hg hf K hK hc
  intro i
  have h₀ := (regularPrincipalBaseChange_homology_isZero_iff a ha (baseChange f K) hS i).mpr
    (scalarCone_homology_isZero_of_repeated_completion_acyclic a (baseChange f K) h i)
  exact h₀.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso
    (baseChangeCompIso f (Ideal.Quotient.mk (Ideal.span {a})) K)).symm

end SerrePositivity
