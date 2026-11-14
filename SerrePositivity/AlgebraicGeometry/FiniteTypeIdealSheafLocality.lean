module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheaf
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：有限型イデアル層のアフィン判定と有限和。
方針：既存の切断イデアルの制限と、有限生成性の像・和による保存を使う。
規約：Noether 性を要求しない。
使われ方：C02 のアフィンでの有限生成部分イデアルを大域イデアル層へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- アフィンスキームでは、全体の切断イデアルが有限生成ならイデアル層は有限型。 -/
theorem isFiniteTypeIdealSheaf_of_fg_top
    {X : Scheme.{u}} [IsAffine X] (K : X.IdealSheafData)
    (hK : (K.ideal ⟨⊤, isAffineOpen_top X⟩).FG) : IsFiniteTypeIdealSheaf K := by
  intro U
  rw [← K.map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) (show U.1 ≤ ⊤ from le_top)]
  exact hK.map _

/-- 有限生成な大域切断イデアルから作ったイデアル層は有限型。 -/
theorem isFiniteTypeIdealSheaf_ofIdealTop
    {X : Scheme.{u}} (I : Ideal Γ(X, ⊤)) (hI : I.FG) :
    IsFiniteTypeIdealSheaf (Scheme.IdealSheafData.ofIdealTop I) := by
  intro U
  change (I.map (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom).FG
  exact hI.map _

/-- 有限型な二つのイデアル層の和は有限型。 -/
theorem IsFiniteTypeIdealSheaf.sup
    {X : Scheme.{u}} {K L : X.IdealSheafData}
    (hK : IsFiniteTypeIdealSheaf K) (hL : IsFiniteTypeIdealSheaf L) :
    IsFiniteTypeIdealSheaf (K ⊔ L) := by
  intro U
  change (K.ideal U ⊔ L.ideal U).FG
  exact Submodule.FG.sup (hK U) (hL U)

end SerrePositivity.AlgebraicGeometry
