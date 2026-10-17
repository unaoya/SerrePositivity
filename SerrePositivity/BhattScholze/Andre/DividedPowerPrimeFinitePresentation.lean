module

public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimeFiniteUniversal
public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimeGenerators

/-!
# André E1・E2：有限切断多項式表示の分冪評価の単射性

## 概要

有限個の変数の p 乗を零とした多項式商を有限テンソル段と同定し、
標準分冪評価の単射性を証明する。BS Rem 7.15(1)（著者版 p.62）。

## 方針

両者の変数による普遍性から互いに逆な射を作り、テンソル段の単射評価を移す。

## 規約

表示の同型には標数は不要。分冪評価には p の素数性と係数環内で p=0 を使う。

## 使われ方

可算切断表示の単射性を多項式の有限変数支持により得るために使う。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p n : ℕ)
local notation "J" => monicPowerFamilyRelationIdeal p (Fin n) A (fun _ => 0)

/-- 概要：n 個の変数の p 乗を零にした通常多項式商。
方針：既存のモニック冪関係イデアルの右辺を零にする。
規約：p=0 と零係数環も定義に含める。
使われ方：BS Rem 7.15(1)（著者版 p.62）の有限切断表示。 -/
abbrev DividedPowerPrimeFiniteAlgebra := MvPolynomial (Fin n) A ⧸ J

/-- 概要：有限切断多項式商から有限テンソル段への標準射。
方針：テンソル段の各変数の p 乗消滅を使い評価を商へ降ろす。
規約：係数環作用を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の順射。 -/
def dividedPowerPrimeFiniteToTensor :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A]
      dividedPowerPrimeTensorStage (A := A) p n := by
  let g : MvPolynomial (Fin n) A →ₐ[A] dividedPowerPrimeTensorStage (A := A) p n :=
    MvPolynomial.aeval (dividedPowerPrimeTensorStageRoot (A := A) p n)
  apply Ideal.Quotient.liftₐ _ g
  have hker : J ≤ RingHom.ker g.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g (MvPolynomial.X i ^ p - MvPolynomial.C (0 : A)) = 0
    simp [g, dividedPowerPrimeTensorStageRoot_pow]
  exact fun _ hx => hker hx

/-- 概要：有限切断表示の順射は変数を同じ番号のテンソル変数へ送る。
方針：商からの多項式評価の公式を使う。
規約：変数番号を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の逆写像の確認。 -/
theorem dividedPowerPrimeFiniteToTensor_X (i : Fin n) :
    dividedPowerPrimeFiniteToTensor (A := A) p n (Ideal.Quotient.mk J (MvPolynomial.X i)) =
      dividedPowerPrimeTensorStageRoot (A := A) p n i := by
  simp [dividedPowerPrimeFiniteToTensor]

/-- 概要：有限テンソル段から有限切断多項式商への標準射。
方針：商の変数の p 乗消滅を有限テンソル段の普遍射へ渡す。
規約：標数仮定を使わない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の逆射。 -/
def dividedPowerPrimeTensorToFinite : dividedPowerPrimeTensorStage (A := A) p n →ₐ[A]
    DividedPowerPrimeFiniteAlgebra (A := A) p n :=
  dividedPowerPrimeTensorStageLift (A := A) p n (fun i => Ideal.Quotient.mk J (MvPolynomial.X i))
    (fun i => by
      simpa only [map_zero] using
        (monicPowerFamilyQuotient_root_pow p (Fin n) A (fun _ => 0) i))

/-- 概要：有限切断表示からテンソル段へ移して戻すと元に戻る。
方針：商と多項式の射の外延性を使い、各変数で合成を確認する。
規約：係数環を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示の独立性。 -/
theorem dividedPowerPrimeTensorToFinite_comp_toTensor :
    (dividedPowerPrimeTensorToFinite (A := A) p n).comp
      (dividedPowerPrimeFiniteToTensor p n) = AlgHom.id A _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change dividedPowerPrimeTensorToFinite p n
    (dividedPowerPrimeFiniteToTensor p n (Ideal.Quotient.mk J (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToTensor_X]
  exact dividedPowerPrimeTensorStageLift_root (A := A) p n _ _ i

/-- 概要：テンソル段から有限切断表示へ移して戻しても元に戻る。
方針：テンソル段の変数上の外延性と普遍射の値を使う。
規約：係数環に非零性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の検証。 -/
theorem dividedPowerPrimeFiniteToTensor_comp_toFinite :
    (dividedPowerPrimeFiniteToTensor (A := A) p n).comp
      (dividedPowerPrimeTensorToFinite p n) = AlgHom.id A _ := by
  apply dividedPowerPrimeTensorStageHom_ext
  intro i
  change dividedPowerPrimeFiniteToTensor p n
    (dividedPowerPrimeTensorToFinite p n (dividedPowerPrimeTensorStageRoot p n i)) = _
  rw [show dividedPowerPrimeTensorToFinite p n (dividedPowerPrimeTensorStageRoot p n i) =
      Ideal.Quotient.mk J (MvPolynomial.X i) from
        dividedPowerPrimeTensorStageLift_root (A := A) p n _ _ i]
  exact dividedPowerPrimeFiniteToTensor_X p n i

/-- 概要：有限切断多項式商は有限反復テンソル段と係数代数として同型。
方針：互いに逆であることを確認した具体的な二射を束ねる。
規約：素数性と標数はこの同型には不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断多項式の独立性の移送。 -/
def dividedPowerPrimeFiniteTensorEquiv : DividedPowerPrimeFiniteAlgebra (A := A) p n ≃ₐ[A]
    dividedPowerPrimeTensorStage (A := A) p n :=
  AlgEquiv.ofAlgHom (dividedPowerPrimeFiniteToTensor p n) (dividedPowerPrimeTensorToFinite p n)
    (dividedPowerPrimeFiniteToTensor_comp_toFinite p n)
    (dividedPowerPrimeTensorToFinite_comp_toTensor p n)

/-- 概要：有限切断多項式商の標準分冪評価射。
方針：表示同型を有限テンソル段の標準評価と合成する。
規約：p は素数で係数環内で零。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算表示の有限支持への制限。 -/
def dividedPowerPrimeFiniteEval [Fact p.Prime] (hp : (p : A) = 0) :
    DividedPowerPrimeFiniteAlgebra (A := A) p n →ₐ[A] DividedPowerAlgebra A A :=
  (dividedPowerPrimeTensorStageEval p hp n).comp (dividedPowerPrimeFiniteToTensor p n)

/-- 概要：有限切断評価は変数 i を γₚⁱ へ送る。
方針：表示射の変数公式とテンソル段の分冪評価を使う。
規約：変数の番号は Fin n の自然数値を使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算評価との互換性。 -/
theorem dividedPowerPrimeFiniteEval_X [Fact p.Prime] (hp : (p : A) = 0) (i : Fin n) :
    dividedPowerPrimeFiniteEval p n hp (Ideal.Quotient.mk J (MvPolynomial.X i)) =
      DividedPowerAlgebra.dp A (p ^ (i : ℕ)) (1 : A) := by
  change dividedPowerPrimeTensorStageEval p hp n
    (dividedPowerPrimeFiniteToTensor p n (Ideal.Quotient.mk J (MvPolynomial.X i))) = _
  rw [dividedPowerPrimeFiniteToTensor_X, dividedPowerPrimeTensorStageEval_root]

/-- 概要：有限切断多項式商から一元分冪代数への標準評価は単射。
方針：表示同型と有限テンソル段の単射評価を合成する。
規約：追加の平坦性や係数環の非零性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の可算表示の単射性の有限段。 -/
theorem dividedPowerPrimeFiniteEval_injective [Fact p.Prime] (hp : (p : A) = 0) :
    Function.Injective (dividedPowerPrimeFiniteEval (A := A) p n hp) :=
  (dividedPowerPrimeTensorStageEval_injective p hp n).comp
    (dividedPowerPrimeFiniteTensorEquiv (A := A) p n).injective

end SerrePositivity.BhattScholze.Andre
