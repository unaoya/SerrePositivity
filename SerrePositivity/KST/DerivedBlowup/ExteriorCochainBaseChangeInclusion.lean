module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainBaseChange
public import SerrePositivity.KST.DerivedBlowup.ExteriorInclusionTransport

/-!
概要：KST Def3.1 の底変更 cochain 複体の各項を総外積の tensor に含める。
方針：元の複体の同次包含を tensor し、標準次数同型で評価する。
規約：係数環の代数構造は環準同型から取る。
使われ方：底変更 cochain 同型の乗法・単位保存の検証。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：底変更 cochain の各項から総外積の tensor への包含。
方針：元の同次包含を tensor する。
規約：KST Def3.1。使われ方：乗法保存を検証する比較先。 -/
def exteriorBaseChangeCochainInclusion (φ : R →+* S) (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    (baseChange φ (exteriorKoszulCochain d)).X q →ₗ[S] S ⊗[R] ExteriorAlgebra R M := by
  letI := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
    (exteriorCochainInclusion d q) :
      S ⊗[R] (exteriorKoszulCochain d).X q →ₗ[S] S ⊗[R] ExteriorAlgebra R M)

/-- 概要：負次数の標準同型の逆に沿う tensor 包含の公式。
方針：純粋 tensor で元の包含の標準同型公式を使う。
規約：KST Def3.1。使われ方：底変更 cochain 同型の総外積での評価。 -/
theorem exteriorBaseChangeCochainInclusion_standard_inv (φ : R →+* S)
    (d : M →ₗ[R] R) (n : ℕ) :
    letI := φ.toAlgebra
    ∀ z : S ⊗[R] ExteriorAlgebra.exteriorPower R n M,
      exteriorBaseChangeCochainInclusion φ d (-(n : ℤ))
          ((ModuleCat.extendScalars φ).map (exteriorKoszulCochainXIso d n).inv z) =
        exteriorBaseChangeDegreeInclusion n z := by
  let := φ.toAlgebra
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    change s ⊗ₜ[R] exteriorCochainInclusion d (-(n : ℤ))
        ((exteriorKoszulCochainXIso d n).inv z) = s ⊗ₜ[R] z.val
    rw [exteriorCochainInclusion_standard_inv]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 概要：cochain 底変更同型の総外積での値は構成済みの代数底変更射。
方針：負次数の標準同型公式と同次底変更の包含公式を使う。
規約：KST Def3.1。使われ方：dg 代数の単位と乗法保存。 -/
theorem exteriorBaseChangeCochainInclusion_iso (φ : R →+* S) (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    ∀ z : (exteriorKoszulCochain (exteriorBaseChangeDifferential (S := S) d)).X q,
      exteriorBaseChangeCochainInclusion φ d q
          ((exteriorCochainBaseChangeIso φ d).hom.f q z) =
        exteriorToBaseChange
          (exteriorCochainInclusion (exteriorBaseChangeDifferential (S := S) d) q z) := by
  let := φ.toAlgebra
  intro z
  by_cases hq : q ≤ 0
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, q = -(n : ℤ) := ⟨(-q).toNat, by omega⟩
    subst q
    change exteriorBaseChangeCochainInclusion φ d (-(n : ℤ))
      ((exteriorCochainBaseChangeXIso φ d (-(n : ℤ))).hom z) = _
    rw [exteriorCochainBaseChangeXIso_neg]
    change exteriorBaseChangeCochainInclusion φ d (-(n : ℤ))
      ((ModuleCat.extendScalars φ).map (exteriorKoszulCochainXIso d n).inv
        (exteriorDegreeToBaseChange n
          ((exteriorKoszulCochainXIso (exteriorBaseChangeDifferential (S := S) d) n).hom z))) = _
    rw [exteriorBaseChangeCochainInclusion_standard_inv, exteriorDegreeToBaseChange_inclusion]
    rw [exteriorCochainInclusion_neg]
    rfl
  · have := ModuleCat.subsingleton_of_isZero
      (exteriorKoszulCochain_isZero_X_pos (exteriorBaseChangeDifferential (S := S) d) q
        (lt_of_not_ge hq))
    have hz : z = 0 := Subsingleton.elim _ _
    rw [hz, map_zero, map_zero, map_zero, map_zero]

/-- 概要：逆 cochain 底変更同型の総外積での値は逆代数底変更射。
方針：順代数同型の単射性で比較し、順 cochain 比較と逆元律を使う。
規約：KST Def3.1。使われ方：底変更 dg 関手の単位・乗法保存。 -/
theorem exteriorBaseChangeCochainInclusion_iso_inv (φ : R →+* S)
    (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    ∀ z : (baseChange φ (exteriorKoszulCochain d)).X q,
      exteriorCochainInclusion (exteriorBaseChangeDifferential (S := S) d) q
          ((exteriorCochainBaseChangeIso φ d).inv.f q z) =
        exteriorOfBaseChange (exteriorBaseChangeCochainInclusion φ d q z) := by
  let := φ.toAlgebra
  intro z
  apply (exteriorBaseChangeEquiv (R := R) (S := S) (M := M)).injective
  change exteriorToBaseChange
      (exteriorCochainInclusion (exteriorBaseChangeDifferential (S := S) d) q
        ((exteriorCochainBaseChangeIso φ d).inv.f q z)) =
    exteriorToBaseChange (exteriorOfBaseChange (exteriorBaseChangeCochainInclusion φ d q z))
  rw [← exteriorBaseChangeCochainInclusion_iso]
  have hi := congrArg (fun f => f.f q) (exteriorCochainBaseChangeIso φ d).inv_hom_id
  have hz := congr($(hi).hom z)
  change (exteriorCochainBaseChangeIso φ d).hom.f q
    ((exteriorCochainBaseChangeIso φ d).inv.f q z) = z at hz
  rw [hz]
  exact (AlgHom.congr_fun exteriorToBaseChange_comp_of
    (exteriorBaseChangeCochainInclusion φ d q z)).symm

/-- 概要：底変更 cochain の総外積 tensor への包含は全整数次数で単射。
方針：底変更複体同型を逆に使い、元の包含と総代数同型の単射性へ帰着する。
規約：KST Def3.1、平坦性不要。使われ方：dg 代数の乗法保存を検証する。 -/
theorem exteriorBaseChangeCochainInclusion_injective (φ : R →+* S)
    (d : M →ₗ[R] R) (q : ℤ) :
    letI := φ.toAlgebra
    Function.Injective (exteriorBaseChangeCochainInclusion φ d q) := by
  let := φ.toAlgebra
  intro x y hxy
  apply (ModuleCat.mono_iff_injective ((exteriorCochainBaseChangeIso φ d).inv.f q)).mp
    inferInstance
  apply exteriorCochainInclusion_injective (exteriorBaseChangeDifferential (S := S) d) q
  apply (exteriorBaseChangeEquiv (R := R) (S := S) (M := M)).injective
  change exteriorToBaseChange
      (exteriorCochainInclusion (exteriorBaseChangeDifferential (S := S) d) q
        ((exteriorCochainBaseChangeIso φ d).inv.f q x)) =
    exteriorToBaseChange
      (exteriorCochainInclusion (exteriorBaseChangeDifferential (S := S) d) q
        ((exteriorCochainBaseChangeIso φ d).inv.f q y))
  rw [← exteriorBaseChangeCochainInclusion_iso, ← exteriorBaseChangeCochainInclusion_iso]
  have hi (z : (baseChange φ (exteriorKoszulCochain d)).X q) :
      (exteriorCochainBaseChangeIso φ d).hom.f q
        ((exteriorCochainBaseChangeIso φ d).inv.f q z) = z := by
    have h := congrArg (fun f => f.f q) (exteriorCochainBaseChangeIso φ d).inv_hom_id
    exact congr($(h).hom z)
  rw [hi, hi, hxy]

end SerrePositivity.KST.DerivedBlowup
