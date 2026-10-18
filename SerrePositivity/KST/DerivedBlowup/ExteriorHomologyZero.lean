module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationBoundary
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
概要：KST Def3.1 の外積 Koszul 模型の H⁰ を微分像による商に標準同定する。
方針：零微分により H⁰ を opcycles とし、境界像の計算を商線形同型へ移す。
規約：微分の正則性や解消性を仮定しない。H⁰ 同型は構成を明示する。
使われ方：普遍チャートの標準添加射の擬同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：次数0境界像の商と微分 d の像の商の標準線形同型。
方針：次数0項の基底環同型と境界像の等式を商へ降ろす。
規約：KST Def3.1。使われ方：opcycles の明示表示。 -/
def exteriorBoundaryQuotientEquiv (d : M →ₗ[R] R) :
    ((exteriorKoszulCochain d).X 0 ⧸
      LinearMap.range ((exteriorKoszulCochain d).d (-1) 0).hom) ≃ₗ[R]
        R ⧸ LinearMap.range d :=
  Submodule.Quotient.equiv _ _ (exteriorCochainZeroIso d).toLinearEquiv (by
    rw [← LinearMap.range_comp]
    exact exteriorBoundary_range d)

/-- 概要：次数0 opcycles と R/im d の標準同型。
方針：ModuleCat の opcycles の商表示と境界商同型を合成する。
規約：KST Def3.1。使われ方：H⁰ と係数商の同定。 -/
def exteriorOpcyclesZeroIso (d : M →ₗ[R] R) :
    (exteriorKoszulCochain d).opcycles 0 ≅ ModuleCat.of R (R ⧸ LinearMap.range d) :=
  (exteriorKoszulCochain d).opcyclesIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
    ((exteriorKoszulCochain d).sc' (-1) 0 1).moduleCatOpcyclesIso ≪≫
    (exteriorBoundaryQuotientEquiv d).toModuleIso

/-- 概要：opcycles の標準同型は次数0の商射と可換。
方針：ModuleCat の商表示の射影公式と quotient equiv の定義を使う。
規約：KST Def3.1。使われ方：標準添加射の H⁰ 作用の計算。 -/
theorem exteriorOpcyclesZeroIso_projection (d : M →ₗ[R] R) :
    (exteriorKoszulCochain d).pOpcycles 0 ≫ (exteriorOpcyclesZeroIso d).hom =
      (exteriorCochainZeroIso d).hom ≫ ModuleCat.ofHom (LinearMap.range d).mkQ := by
  dsimp only [exteriorOpcyclesZeroIso, Iso.trans_hom]
  rw [HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc,
    ShortComplex.pOpcycles_comp_moduleCatOpcyclesIso_hom_assoc]
  rfl

/-- 概要：Koszul 外積複体の H⁰ と R/im d の選択に依存しない標準同型。
方針：次数0から出る微分が零なので H⁰ と opcycles の標準同型を使う。
規約：KST Def3.1。使われ方：関係式商への標準添加射の可逆性。 -/
def exteriorHomologyZeroIso (d : M →ₗ[R] R) :
    (exteriorKoszulCochain d).homology 0 ≅ ModuleCat.of R (R ⧸ LinearMap.range d) :=
  (exteriorKoszulCochain d).isoHomologyι 0 1 (by simp)
    ((exteriorKoszulCochain_isZero_X_pos d 1 (by omega)).eq_of_tgt _ _) ≪≫
      exteriorOpcyclesZeroIso d

end SerrePositivity.KST.DerivedBlowup
