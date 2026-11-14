module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntRestriction
public import SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinementQuasiIso

/-!
概要：構造層の有限アフィン細分の同型性を、実際の環の Frobenius 順極限後に供給する。
方針：2e の準連接層の比較を整数へ制限し、同じ環の Frobenius 系に渡す。
規約：細分写像の同型性や完全性を、結論の仮定として足さない。
使われ方：F8 の共通アフィン細分と係数前層の自然性の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u v
section Restriction
variable {X : Type u} [TopologicalSpace X] {B : Type v} [CommRing B]
variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 整数への係数制限は、実際の細分写像の Čech H の同型性を保つ。 -/
theorem openCoverCechIntRestriction_refinement_quasiIsoAt
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} B)
    (U : ι → Opens X) (V : κ → Opens X) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) (q : ℕ)
    (h : QuasiIsoAt (openCoverCechRefinementMap P U V ρ hρ) q) :
    QuasiIsoAt (openCoverCechRefinementMap
      (P ⋙ ModuleCat.restrictScalars (Int.castRingHom B)) U V ρ hρ) q := by
  let S := ModuleCat.restrictScalars (Int.castRingHom B)
  let f := openCoverCechRefinementMap P U V ρ hρ
  let g := openCoverCechRefinementMap (P ⋙ S) U V ρ hρ
  let eU := projectiveCechIntRestrictionComplexIso (openCoverCechDiagram P U)
  let eV := projectiveCechIntRestrictionComplexIso (openCoverCechDiagram P V)
  haveI : QuasiIsoAt f q := h
  have hc : g ≫ eV.hom = eU.hom ≫ (S.mapHomologicalComplex (.up ℕ)).map f := by
    ext n x
    rfl
  haveI : QuasiIsoAt (g ≫ eV.hom) q := by
    rw [hc]
    infer_instance
  exact quasiIsoAt_of_comp_right g eV.hom q

end Restriction

variable (Y : Scheme.{u}) (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)

/-- 構造層の実際の環の Frobenius 系の各段は、構造層の整数係数前層と同型。 -/
def schemeStructureFrobeniusStageIso (n : ℕ) :
    (frobeniusRingSequentialDiagram Y.presheaf p hp hY).obj n ≅
      schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars
        (Int.castRingHom Γ(Y, ⊤)) :=
  NatIso.ofComponents (fun O ↦ LinearEquiv.toModuleIso
    ({ toFun := fun x ↦ x
       invFun := fun x ↦ x
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_add' := fun _ _ ↦ rfl
       map_smul' := by
         intro r x
         change _ = (r : Γ(Y, ⊤)) •
           (show (schemeStructureCechPresheaf Y).obj O from x)
         rw [Int.cast_smul_eq_zsmul] } :
      ((frobeniusRingSequentialDiagram Y.presheaf p hp hY).obj n).obj O ≃ₗ[ℤ]
        (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars
          (Int.castRingHom Γ(Y, ⊤))).obj O)) (by
            intro O V f
            ext x
            rfl)

variable [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]

/-- 構造層の実際の環の Frobenius 順極限後、有限アフィン細分は Čech H の同型。
Stacks 30.2.6 の被覆比較と BST13 Lemma 3.9 の極限に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem schemeStructureFrobeniusCechRefinement_quasiIsoAt
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcover : (⨆ j, V j) = ⊤) (q : ℕ) :
    QuasiIsoAt (openCoverCechRefinementMap
      (frobeniusRingDiagram Y.presheaf p hp hY) U V ρ hρ) q := by
  apply openCoverFrobeniusCechRefinement_quasiIsoAt U V ρ hρ Y.presheaf p hp hY q
  have h : QuasiIsoAt (openCoverCechRefinementMap
      (schemeStructureCechPresheaf Y) U V ρ hρ) q :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).mpr
      (schemeStructureCechRefinement_homologyMap_isIso Y U V ρ hρ hU hV hcover q)
  exact openCoverIntCechRefinement_quasiIsoAt_of_iso U V ρ hρ
    (schemeStructureFrobeniusStageIso Y p hp hY 0).symm q
    (openCoverCechIntRestriction_refinement_quasiIsoAt _ U V ρ hρ q h)

end SerrePositivity.AlgebraicGeometry
