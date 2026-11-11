module

public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulAugmentationZero
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution

/-!
# Koszul 複体の標準一次生成元

## 概要
実際の写像錐模型の零次単位と負一次の生成元を指定し、その微分を計算する。

## 方針
零次の標準包含の同型と、既存の座標作用の零ホモトピーを使う。

## 規約
列の正則性は不要。コチェイン次数の微分は負一次から零次へ向かう。

## 使われ方
BS 著者版 Example 7.9、G-A3-7 の自由分解の差商計算。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 実際の Koszul 複体の零次項と係数環の標準同型。 -/
@[expose] def koszulZeroTermIso : (koszulComplex f).X 0 ≅ ModuleCat.of R R :=
  (asIso ((DerivedCompletion.koszulComplexInclusion R f).f 0)).symm ≪≫
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R)

/-- 零次項の標準単位。 -/
@[expose] def koszulUnitElement : (koszulComplex f).X 0 :=
  (koszulZeroTermIso f).inv (1 : R)

/-- 座標作用の標準零ホモトピーが与える負一次の生成元。 -/
@[expose] def koszulGeneratorElement (i : Fin r) : (koszulComplex f).X (-1) :=
  (DerivedCompletion.koszulComplexCoordinateNullHomotopy R f i).hom 0 (-1)
    (koszulUnitElement f)

/-- 概要：標準生成元の微分は対応する座標と零次単位の積。
方針：座標零ホモトピーの零次成分で、正一次への微分が零であることを使う。
規約：実際の再帰的な写像錐模型の元についての等式。
使われ方：BS 著者版 Example 7.9 の D t̃ = f_i − d z_i。 -/
theorem koszulGeneratorElement_d (i : Fin r) :
    (koszulComplex f).d (-1) 0 (koszulGeneratorElement f i) =
      f i • koszulUnitElement f := by
  have h := scalarNullHomotopy_component
    (DerivedCompletion.koszulComplexCoordinateNullHomotopy R f i) 0 (-1) 1 (by decide) (by decide)
  rw [koszulComplex_d_zero_one, zero_comp, zero_add] at h
  exact congrArg (fun m => m (koszulUnitElement f)) h

/-- 概要：標準生成元の微分を零次座標で読むと、関係の元そのものになる。
方針：標準零次同型で単位を 1 に送り、線形性を適用する。
規約：正則性によらない自由複体の座標公式。
使われ方：BS 著者版 Example 7.9 の余法類の計算。 -/
theorem koszulGeneratorElement_d_coordinate (i : Fin r) :
    (koszulZeroTermIso f).hom
      ((koszulComplex f).d (-1) 0 (koszulGeneratorElement f i)) = f i := by
  rw [koszulGeneratorElement_d]
  change (koszulZeroTermIso f).hom.hom (f i • ((koszulZeroTermIso f).inv (1 : R))) = _
  rw [map_smul]
  have h : (koszulZeroTermIso f).hom ((koszulZeroTermIso f).inv (1 : R)) = (1 : R) :=
    congrArg (fun m => m (1 : R)) (koszulZeroTermIso f).inv_hom_id
  rw [h, smul_eq_mul, mul_one]

/-- 概要：負次数の消滅だけで Koszul 分解の述語が得られる。
方針：正次数の項は零で、零次ホモロジーは常に関係の商と同型である。
規約：BS 著者版 Example 7.9 の Koszul 正則性の仮定との照合。
使われ方：A3 草稿の仮定を通常の Koszul 分解に渡す。 -/
theorem isKoszulResolution_of_negative_homology
    (h : ∀ n : ℕ, Limits.IsZero ((koszulComplex f).homology (-(n + 1 : ℤ)))) :
    IsKoszulResolution f := by
  refine ⟨?_, koszulComplex_homology_zero_equiv f⟩
  intro i hi
  cases i with
  | ofNat n =>
    have hpos : (0 : ℤ) < (n : ℤ) := by
      have hn := Int.natCast_nonneg n
      simp only [Int.ofNat_eq_natCast] at hi
      omega
    simpa only [Int.ofNat_eq_natCast] using
      koszulComplex_isZero_homology_of_pos f (n : ℤ) hpos
  | negSucc n => simpa only [Int.negSucc_eq] using h n

end SerrePositivity
