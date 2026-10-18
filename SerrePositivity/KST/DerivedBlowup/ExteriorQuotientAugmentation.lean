module

public import SerrePositivity.KST.DerivedBlowup.ExteriorHomologyZero
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
概要：KST Def3.1 の微分像の商への標準添加射とその H⁰ 比較。
方針：明示した標準 H⁰ 同型からの射と生成元を零に送る添加射を同定する。
規約：擬同型性には非零次数ホモロジーの消滅だけを必要とする。
使われ方：普遍正則関係式族の cdga 添加射の解消性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：微分像の商では微分の各値が零になる。
方針：商の零判定と線形写像の像への所属を使う。
規約：KST Def3.1。使われ方：微分像の商への標準添加射。 -/
theorem exteriorDifferential_quotient_zero (d : M →ₗ[R] R) (m : M) :
    algebraMap R (R ⧸ LinearMap.range d) (d m) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (LinearMap.mem_range_self d m)

/-- 概要：微分像の商への標準添加射。
方針：生成元を零へ送る添加射に商での微分消滅を与える。
規約：KST Def3.1。使われ方：普遍チャートの商表示への標準射。 -/
def exteriorQuotientAugmentation (d : M →ₗ[R] R) :
    exteriorKoszulCochain d ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R (R ⧸ LinearMap.range d)) :=
  exteriorKoszulAugmentation d (exteriorDifferential_quotient_zero d)

/-- 概要：標準添加射は明示した H⁰ 同型から構成する射に等しい。
方針：mkHomToSingle の次数0入力を比較し、opcycles の射影公式を使う。
規約：KST Def3.1。使われ方：標準添加射の擬同型性を H⁰ 計算へ帰着する。 -/
theorem exteriorQuotientAugmentation_eq_toSingle (d : M →ₗ[R] R) :
    exteriorQuotientAugmentation d =
      SerrePositivity.toSingleOfHomology (exteriorKoszulCochain d)
        ((exteriorKoszulCochain_isZero_X_pos d 1 (by omega)).eq_of_tgt _ _)
        (exteriorHomologyZeroIso d).hom := by
  unfold exteriorQuotientAugmentation exteriorKoszulAugmentation
    SerrePositivity.toSingleOfHomology
  congr 1
  dsimp only [exteriorHomologyZeroIso, Iso.trans_hom]
  rw [Iso.inv_hom_id_assoc, exteriorOpcyclesZeroIso_projection]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact exteriorCochainAugmentationComponent_zero d z

/-- 概要：非零次数のホモロジーが零なら標準添加射は擬同型。
方針：標準 H⁰ 同型を使う射と同定し、既存の単一複体への比較定理を適用する。
規約：KST Lemma3.6。使われ方：普遍正則関係式族の解消から標準射への接続。 -/
theorem exteriorQuotientAugmentation_quasiIso (d : M →ₗ[R] R)
    (h : ∀ q : ℤ, q ≠ 0 → IsZero ((exteriorKoszulCochain d).homology q)) :
    QuasiIso (exteriorQuotientAugmentation d) := by
  rw [exteriorQuotientAugmentation_eq_toSingle]
  exact SerrePositivity.quasiIso_toSingleOfHomology _ _ _ h

end SerrePositivity.KST.DerivedBlowup
