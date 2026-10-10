module

public import SerrePositivity.Paper.Section4.PaperK0Comparison
public import SerrePositivity.Asymptotic.PaperTwist
public import SerrePositivity.GroupTheory.ConjugateSum

/-!
# 降下を入力とした漸近ノルム比較

## 構成

論文の支持圏上の通常の Euler 評価と、T から C へ係数変更した後の
正規化 Euler 評価を比較する。二段階の係数変更の合成則と命題4.5により、
A 側から来る K₀ 類では両評価が一致する。

## 証明の範囲

不変な K₀ 類の正の整数倍が A 側から来ることを明示的な引数に取り、
既存の `conjSum_eq` から共役和の一致を証明する。このファイルに `sorry` はない。
具体的な幾何的仮定からの降下の引用は別ファイルで行う。
長さ関数の G 不変性や C 上の G 作用は仮定しない。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter Asymptotic

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing T] [IsLocalRing T] [Algebra A T] [Module.Finite A T]
  [CommRing C] [Nontrivial C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} (z : Fin e → A)
  (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))
  (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hfin : ∀ v j : ℕ,
    lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
  {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 論文の T 側の支持圏から、C 側への係数変更後に測る正規化 Euler 評価。
パラメータの像を A → C で記述し、塔の等式で二段階の像と同定する。 -/
noncomputable def normalizedPaperEulerOnT :
    TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory →+ ℝ :=
  (paperRankEulerK0 lam ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
    (algebraMap A C ∘ z) (base_ideal_le_radical z hz)
    (fun v _ i ↦ base_koszul_pow_finite z lam hfin v i) U hU hs).comp
      (paperSupportedMap (algebraMap T C) (algebraMap A T ∘ z) (algebraMap A C ∘ z)
        (by funext j; exact (IsScalarTower.algebraMap_apply A T C (z j)).symm))

/-- T 側の通常の Euler 評価。有限 A 代数の Noether 性と閉点の台を用いる。 -/
noncomputable def ordinaryPaperEulerOnT :
    TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory →+ ℝ := by
  letI : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  exact ordinaryPaperEulerK0 (algebraMap A T ∘ z)
    (isArtinianRing_quotient_span_of_finite A T z
      (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs

variable [HasDerivedCategory (ModuleCat.{u} A)]

set_option maxHeartbeats 800000 in
-- 支持部分圏の係数変更と K₀ 評価の型の比較に必要。
/-- 正規化評価を A 側へ引き戻すと、A 側の通常評価の階数倍となる。
係数変更の合成則で直接の A → C に帰着し、証明済みの命題4.5を使う。 -/
theorem normalizedPaperEulerOnT_changeRing
    (hKoszul : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T) :
    (normalizedPaperEulerOnT z lam hz hfin U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z)) =
        (Module.finrank A T : ℝ) •
          ordinaryPaperEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  have hc := paperSupportedMap_comp (s := s) (algebraMap A T) (algebraMap T C)
    z (algebraMap A T ∘ z) (algebraMap A C ∘ z) rfl
    (by funext j; exact (IsScalarTower.algebraMap_apply A T C (z j)).symm)
  have ht : (algebraMap T C).comp (algebraMap A T) = algebraMap A C :=
    (IsScalarTower.algebraMap_eq A T C).symm
  have hc' := hc.trans (paperSupportedMap_congr _ _ _ _ _ rfl ht)
  have hv := congrArg (fun f ↦
    (paperRankEulerK0 lam ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
      (algebraMap A C ∘ z) (base_ideal_le_radical z hz)
      (fun v _ i ↦ base_koszul_pow_finite z lam hfin v i) U hU hs).comp f) hc'
  exact hv.trans (normalizedPaperEulerK0_changeRing z lam hz hKoszul hkz hq hfin U hU hs)


set_option maxHeartbeats 800000 in
-- 支持部分圏の係数変更と K₀ 評価の型の比較に必要。
/-- 命題4.5の二つの階数倍公式から、A 側の像での評価の一致を得る。 -/
theorem paperEuler_agree_on_base
    (hKoszul : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T) :
    let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    (ordinaryPaperEulerK0 (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z)) =
    (normalizedPaperEulerOnT z lam hz hfin U hU hs).comp
      (TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z)) := by
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  exact (ordinaryPaperEulerK0_changeRing z hz hKoszul hres hχ U hU hs).trans
    (normalizedPaperEulerOnT_changeRing z lam hz hfin U hU hs hKoszul hkz hq).symm

set_option maxHeartbeats 800000 in
-- 支持部分圏の係数変更と K₀ 評価の型の比較に必要。
/-- 支持つき K₀ の降下を入力とした、全ての K₀ 類に対する定理4.7。
実際の二つの Euler 評価と、係数変更から構成した群作用について証明する。 -/
theorem normComparison_of_descent
    (hKoszul : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
    (hdesc : ∀ y : TriangulatedK0
        (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory,
      (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : TriangulatedK0 (paperSupportedRank (s := s) z).FullSubcategory),
        0 < n ∧ n • y = TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z) x)
    (y : TriangulatedK0 (paperSupportedRank (s := s) (algebraMap A T ∘ z)).FullSubcategory) :
    let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
    ∑ g : G, ordinaryPaperEulerK0 (algebraMap A T ∘ z)
      (isArtinianRing_quotient_span_of_finite A T z
        (by rw [hz]; exact (maximalIdeal.isMaximal A).isPrime.radical)) U hU hs (g • y) =
    ∑ g : G, normalizedPaperEulerOnT z lam hz hfin U hU hs (g • y) := by
  let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  exact conjSum_eq (TriangulatedK0.map (paperSupportedChangeRing (algebraMap A T) z)) _ _
    (fun x ↦ DFunLike.congr_fun
      (paperEuler_agree_on_base z lam hz hfin U hU hs hKoszul hres hχ hkz hq) x) hdesc y

end SerrePositivity.Section4
