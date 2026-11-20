module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PrincipalBlowupIso
public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAffine

/-!
概要：KST §5、Stacks 080Y の局所的に可逆な中心に沿う blowup の自明性。
方針：正則単項中心のアフィン同型を、基底のアフィン開被覆で局所判定する。
規約：可逆性は被覆上の切断イデアルが正則単項であるという条件で表す。
使われ方：blowup の普遍性と可逆化済み中心の比較。
-/

@[expose] public noncomputable section

universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X : Scheme.{u}} (I : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則単項中心のアフィン開集合上では一般の blowup の構造射は同型。
方針：実際のアフィン局所モデルとの同型を介して正則単項 blowup の同型を移す。
規約：KST §5、Stacks 080Y、基底の Noether 性を要求しない。
使われ方：局所的に可逆な中心での blowup の自明性。
-/
theorem blowupπ_restrict_isIso_of_regular_principal (V : X.affineOpens)
    (b : Γ(X, V.1)) (hreg : b ∈ nonZeroDivisors Γ(X, V.1))
    (hI : I.ideal V = Ideal.span {b}) : IsIso (blowupπ I ∣_ V.1) := by
  have := affineBlowupπ_isIso_of_regular_principal (I.ideal V) b hreg hI
  have h : IsIso ((blowupAffineIso I V).hom ≫ (blowupπ I ∣_ V.1)) := by
    rw [blowupAffineIso_hom_restrict]
    unfold affineBlowupModelπ
    infer_instance
  exact IsIso.of_isIso_comp_left (blowupAffineIso I V).hom (blowupπ I ∣_ V.1)

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心がアフィン開被覆上で正則単項なら、その blowup の構造射は同型。
方針：各アフィン開集合上の同型性を Zariski 局所性で貼り合わせる。
規約：KST §5、Stacks 080Y、被覆と局所生成元のみを仮定する。
使われ方：可逆中心の blowup の自明性の一般スキーム版。
-/
theorem blowupπ_isIso_of_locally_regular_principal {ι : Type v}
    (V : ι → X.affineOpens) (hV : ⨆ i, (V i).1 = ⊤)
    (hI : ∀ i, ∃ b : Γ(X, (V i).1), b ∈ nonZeroDivisors Γ(X, (V i).1) ∧
      I.ideal (V i) = Ideal.span {b}) : IsIso (blowupπ I) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun i => (V i).1) hV
  intro i
  obtain ⟨b, hreg, hb⟩ := hI i
  exact blowupπ_restrict_isIso_of_regular_principal I (V i) b hreg hb

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
