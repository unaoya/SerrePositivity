module

public import SerrePositivity.CLMST.Prop247CanonicalRankDescent
public import SerrePositivity.CLMST.Prop247RankClosedSides
public import SerrePositivity.CLMST.Prop247RankSourceValuation
public import SerrePositivity.CLMST.Prop247FiniteComparisonValuation
public import SerrePositivity.BhattScholze.Perfectoidization.Excision

/-! # Prop 2.4.7：BS の excision による引用の置換

## 概要
既存の実 rank 図式と定 rank の有限比較に BS Cor 8.12 の環の系を適用する。

## 方針
導来完備性と付値環への一意延長を供給し、指定した普遍単位の四角形を保って降下する。

## 規約
外部入力は BS Thm 1.17(1) と Cor 8.12 の既存宣言のみである。

## 使われ方
文献入力 proposition_2_4_7 を同じ署名の証明へ置換する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/--
## 概要
perfectoid 基底上の有限比較は指定された canonical excision 四角形を与える。
## 方針
有限表示から導来完備性を、支持冪条件から付値環への一意延長を得て BS の系を使う。
## 規約
AIC 条件を追加せず、元の四つの環と二つの普遍単位を保持する。
## 使われ方
Prop 2.4.7 の定 rank 成分の条件付き組立てに供給する。
-/
theorem prop247_finiteComparison_excision
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) : KLFiniteComparisonExcision R p := by
  intro A B C D _ _ _ _ _ _ _ _ _ _ _ _ a q hq hk hc f g hf hg
  have hA : IsModuleComplete A (p : A) (ModuleCat.of A A) := by
    simpa only [map_natCast] using
      (isModuleComplete_algebraMap_iff R A (p : R) A).mpr
        (prop247_source_isModuleComplete R A p hR)
  have hB : IsModuleComplete B (p : B) (ModuleCat.of B B) := by
    simpa only [map_natCast] using
      (isModuleComplete_algebraMap_iff R B (p : R) B).mpr
        (prop247_source_isModuleComplete R B p hR)
  apply BhattScholze.klCanonicalExcisionSquare_of_excision R p hR A B C D q a f g hf hg
    hA hB (isModuleComplete_principal_ideal A (p : A) (algebraMap R A a) hA)
  intro V _ _ _ _ _ k hI
  let : Algebra A V := k.toAlgebra
  exact prop247_finiteComparison_valuation_extension a q hq hk hc V hI

/--
## 概要
有限・有限表示な S の指定 perfectoid 化への錐は、エタールな主開集合の補集合に支持される。
## 方針
実 rank データを選び、完備性と付値環への一意延長から BS excision を供給して元の錐へ降下する。
## 規約
有界 p 冪ねじれは既存の完備底変換に用い、指定した f の変更はしない。
## 使われ方
標準 perfectoid 化に特殊化して Prop 2.4.7 を証明する。
-/
theorem prop247_isogeny_of_specified
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, ∀ s : S,
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) :
    ∃ N : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ N) = 0 := by
  obtain ⟨B, hB, hAIC, _hflat, P, β, hβ, t, ht, T, u, hu, Q, γ, hγ,
    hProduct, hdescent⟩ := prop247_exists_canonical_generalRank_descent_data R S C p hR
      (fun B _ hB _ => prop247_finiteComparison_excision B p hB) f hf hbounded g hetale
  let hetaleB := etaleAway_tensor_baseChange (R := R) (A := S) (B := B) g hetale
  let (n : t) : Algebra
      (prop247_rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    (u n).toRingHom.toAlgebra
  let (n : t) : IsScalarTower B
      (prop247_rankSourceImage B (B ⊗[R] S) (algebraMap R B g) hetaleB n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsIntegralPerfectoid (T n) p := (hu n).1
  obtain ⟨hA, hX, hI, _⟩ := prop247_rankSource_closedSide_completeness
    B (B ⊗[R] S) p hB (algebraMap R B g) (fun n => T n) hT
  have hPB : KLCanonicalExcisionSquare hβ hProduct
      (prop247_rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g) := by
    apply BhattScholze.klCanonicalExcisionSquare_of_excision B p hB
      (B ⊗[R] S) ((n : t) → T n ⊗[B] (B ⊗[R] S)) P ((n : t) → Q n)
      (prop247_rankTensorUnit B (B ⊗[R] S) (fun n => T n)) (algebraMap R B g)
      β (prop247_rankProductUnit B (B ⊗[R] S) (fun n => T n) (fun n => Q n) γ)
      hβ hProduct hA hX hI
    intro V _ _ _ _ _ k hk
    let : Algebra (B ⊗[R] S) V := k.toAlgebra
    have hg : k (algebraMap B (B ⊗[R] S) (algebraMap R B g)) ≠ 0 := by
      simpa only [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker] using hk
    exact prop247_aic_rankSourceProduct_valuation_extension B (B ⊗[R] S) p hB hAIC
      (algebraMap R B g) hetaleB t ht (fun n => T n) hu V hg
  obtain ⟨N, hN, _⟩ := hdescent hPB
  exact ⟨N, hN⟩

/--
## 概要
CLMST Prop 2.4.7：標準 perfectoid 化への実導来錐は J-isogeny である。
## 方針
各 g の主開集合でのエタール性に指定単位版の降下定理を適用する。
## 規約
文献入力と同じ署名を保ち、有界ねじれ以外の追加仮定を置かない。
## 使われ方
CLMST.Inputs.proposition_2_4_7 の証明と専用依存監査の公開入口である。
-/
theorem proposition_2_4_7_proved
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (J : Ideal R) (hJ : J.FG)
    (hEtale : ∀ g ∈ J, let _ := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (hbounded : ∃ N : ℕ, ∀ (n : ℕ) (s : S),
      (p : S) ^ n * s = 0 → (p : S) ^ N * s = 0) :
    ∀ g ∈ J, ∃ N : ℕ,
      moduleMapConeScalar R (perfectoidizationModuleMap R S p hR) (g ^ N) = 0 := by
  clear hJ
  intro g hg
  exact prop247_isogeny_of_specified R S (Perfectoidization R S p hR) p hR
    (IsScalarTower.toAlgHom R S (Perfectoidization R S p hR))
    (isPerfectoidization_toPerfectoidization R S p hR) hbounded g (hEtale g hg)

end SerrePositivity.CLMST
