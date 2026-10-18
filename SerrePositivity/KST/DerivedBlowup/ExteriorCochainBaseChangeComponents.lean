module

public import SerrePositivity.KST.DerivedBlowup.ExteriorChainBaseChange
public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerInclusion

/-!
概要：KST Def3.1 の整数次数外積複体の底変更の項同型。
方針：非正次数は同次外積の底変更、正次数は零対象性を使う。
規約：係数環の代数構造は環準同型で固定する。
使われ方：Koszul cochain 複体の底変更同型の成分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：整数 Koszul 複体の底変更を各次数で比較する同型。
方針：非正次数の標準同型と次数別底変更を合成し、正次数では零対象の同型を取る。
規約：KST Def3.1。使われ方：整数 cochain の底変更比較。 -/
def exteriorCochainBaseChangeXIso (φ : R →+* S) (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d)).X q ≅
      (baseChange φ (exteriorKoszulCochain d)).X q := by
  letI := φ.toAlgebra
  by_cases hq : q ≤ 0
  · exact exteriorCochainXIsoNonpos (exteriorBaseChangeDifferential (S := S) d) q hq ≪≫
      (exteriorDegreeBaseChangeEquiv (R := R) (S := S) (M := M) (-q).toNat).toModuleIso ≪≫
        ((ModuleCat.extendScalars φ).mapIso (exteriorCochainXIsoNonpos d q hq)).symm
  · exact (exteriorKoszulCochain_isZero_X_pos (exteriorBaseChangeDifferential (S := S) d) q
      (lt_of_not_ge hq)).iso
        ((ModuleCat.extendScalars φ).map_isZero
          (exteriorKoszulCochain_isZero_X_pos d q (lt_of_not_ge hq)))

/-- 概要：負の自然数次数での底変更項同型の公式。
方針：非正次数の分岐を計算する。
規約：KST Def3.1。使われ方：零延長の微分との比較。 -/
theorem exteriorCochainBaseChangeXIso_neg (φ : R →+* S) (d : M →ₗ[R] R) (n : ℕ) :
    letI := φ.toAlgebra
    exteriorCochainBaseChangeXIso φ d (-(n : ℤ)) =
      exteriorKoszulCochainXIso (exteriorBaseChangeDifferential (S := S) d) n ≪≫
        (exteriorDegreeBaseChangeEquiv (R := R) (S := S) (M := M) n).toModuleIso ≪≫
          ((ModuleCat.extendScalars φ).mapIso (exteriorKoszulCochainXIso d n)).symm := by
  cases n with
  | zero => rfl
  | succ n => rfl

end SerrePositivity.KST.DerivedBlowup
