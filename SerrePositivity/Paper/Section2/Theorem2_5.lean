module

public import SerrePositivity.Paper.Section2.LengthAlgebraConstruction
public import SerrePositivity.Paper.Section2.LengthAlgebraConsequences

/-!
# 定理2.5：標数別の構成からの導出

補題2.2の具体的な基底の情報を明示的に受け取る。
標数別の存在証明は `LengthAlgebraConstruction`、
パラメータの冪と階数への共通の導出は `LengthAlgebraConsequences` に分離する。
等標数は Roberts、混標数は Bhatt–Scholze と CLMST の名前付き引用から構成を導く。
-/

public section
universe u
open IsLocalRing
open scoped ENNReal
namespace SerrePositivity
namespace Section2

/-- 定理2.5。補題2.2の具体的な基底の情報で標数を分け、標数別の構成を呼ぶ。
冪への拡張と階数公式は証明済みの共通の導出を使う。この定理自体に直接の `sorry` はないが、
Roberts・Bhatt–Scholze・CLMST・正規化長さの引用に依存する。正則パラメータと重複度公式は証明済み。 -/
theorem theorem_2_5 (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    (hbase :
      (CharP D p ∧ ∃ e : A ≃+* MvPowerSeries (Fin h) (ResidueField D),
        ∀ i, e (t i) = MvPowerSeries.X i) ∨
      (CharZero D ∧ t ⟨0, hpos⟩ = (p : A) ∧
        ∃ e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)),
          ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra D C)
      (_ : Algebra (Tower A t p) C) (_ : IsScalarTower A D C)
      (_ : IsScalarTower A (Tower A t p) C),
      -- (2.4)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p C).len
          (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0) ∧
      -- (2.5)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
          ENNReal.ofReal ((v : ℝ) ^ h *
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ))) ∧
      -- (2.6)
      (∀ v : ℕ, 0 < v →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
          ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞)) := by
  have hex : ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra D C)
      (_ : Algebra (Tower A t p) C) (_ : IsScalarTower A D C)
      (_ : IsScalarTower A (Tower A t p) C),
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p C).len
          (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
    rcases hbase with ⟨hp, _, _⟩ | ⟨hzero, htp, e, he⟩
    · let := hp
      exact lengthAlgebra_equalCharacteristic A D hinj hsep hres t hdimA hdimD
        hpos ht p
    · let := hzero
      exact lengthAlgebra_mixedCharacteristic A D hinj hres t hdimA hdimD
        hpos ht hsop p htp e he
  obtain ⟨C, cRing, aAlg, dAlg, towerAlg, adTower, atTower, hzero, hquot⟩ := hex
  refine ⟨C, cRing, aAlg, dAlg, towerAlg, adTower, atTower, ?_, ?_, ?_⟩
  · intro z hz v hv i hi
    exact hzero (fun j ↦ z j ^ v) (hz.pow D v hv) i hi
  · exact parameter_quotient_values_pow D C (towerLengthOn A D hinj t p C) hquot
  · exact base_parameter_values_of_multiplicity A D C hinj hres t ht hdimA hsop
      (towerLengthOn A D hinj t p C)
      (parameter_quotient_values_pow D C (towerLengthOn A D hinj t p C) hquot)

end Section2

end SerrePositivity
