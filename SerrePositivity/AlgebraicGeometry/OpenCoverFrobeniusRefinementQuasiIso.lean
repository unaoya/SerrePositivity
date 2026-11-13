module

public import SerrePositivity.AlgebraicGeometry.OpenCoverSequentialCech
public import SerrePositivity.AlgebraicGeometry.FrobeniusRingSequentialDiagram

/-!
概要：実際の環の前層の細分の同型性を、Frobenius 順極限後へ渡す。
方針：有限段の細分を順極限へ渡し、環の順極限との自然同型で移送する。
規約：完全性は有限段で供給し、順極限後に仮定し直さない。
使われ方：F8 の全複体の共通アフィン細分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable (U : ι → Opens X) (V : κ → Opens X)
variable (ρ : κ → ι) (hρ : ∀ j, V j ≤ U (ρ j))

/-- 係数前層の同型に沿う、同じ細分写像の Čech H の同型性の移送。 -/
theorem openCoverIntCechRefinement_quasiIsoAt_of_iso
    {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} ℤ} (e : P ≅ Q) (q : ℕ)
    (h : QuasiIsoAt (openCoverCechRefinementMap P U V ρ hρ) q) :
    QuasiIsoAt (openCoverCechRefinementMap Q U V ρ hρ) q := by
  let CU := openCoverIntCechFunctor U
  let CV := openCoverIntCechFunctor V
  let eU := CU.mapIso e
  let eV := CV.mapIso e
  haveI : QuasiIsoAt (openCoverCechRefinementMap P U V ρ hρ) q := h
  have hc : openCoverCechRefinementMap P U V ρ hρ ≫ eV.hom =
      eU.hom ≫ openCoverCechRefinementMap Q U V ρ hρ :=
    openCoverCechRefinementMap_naturality U V ρ hρ e.hom
  haveI : QuasiIsoAt (eU.hom ≫ openCoverCechRefinementMap Q U V ρ hρ) q := by
    rw [← hc]
    infer_instance
  exact quasiIsoAt_of_comp_left eU.hom _ q

variable [Fintype ι] [Fintype κ]
variable (P : (Opens X)ᵒᵖ ⥤ CommRingCat.{v}) (p : ℕ) (hp : p.Prime)
variable (hP : ∀ O, (p : P.obj O) = 0)

/-- 有限段の細分が Čech H の同型なら、実際の環の Frobenius 順極限後も同型。
Stacks 30.2.6 の被覆比較と BST13 Lemma 3.9 の極限に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem openCoverFrobeniusCechRefinement_quasiIsoAt (q : ℕ)
    (h : QuasiIsoAt (openCoverCechRefinementMap
      ((frobeniusRingSequentialDiagram P p hp hP).obj 0) U V ρ hρ) q) :
    QuasiIsoAt (openCoverCechRefinementMap
      (frobeniusRingDiagram P p hp hP) U V ρ hρ) q := by
  let S := frobeniusRingSequentialDiagram P p hp hP
  have hs : QuasiIsoAt (openCoverCechRefinementMap (colimit S) U V ρ hρ) q :=
    openCoverSequentialCech_refinement_quasiIsoAt S U V ρ hρ q (fun _ ↦ h)
  exact openCoverIntCechRefinement_quasiIsoAt_of_iso U V ρ hρ
    (frobeniusRingSequentialColimitIso P p hp hP) q hs

end SerrePositivity.AlgebraicGeometry
