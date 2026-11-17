module

public import SerrePositivity.AlgebraicGeometry.OpenFamilyCechComparison

/-!
概要：同じ開の細分を、元の混合積とタプル開の標準比較で保つ。
方針：元の開の包含を各射影に合成し、普遍性と開埋め込みの一意性を使う。
規約：元の被覆と添字の写像、元の nerve への入射を保持する。
使われ方：矩形の交叉の次数を動かす二重 Čech の係数の自然性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι κ : Type}
variable (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι) (hV : ∀ j, V j ≤ U (ρ j))

include hV in
/-- 同じ開の細分は、元のタプル開の包含を与える。 -/
theorem openFamilyCechRefinementOpen_le (n : SimplexCategory) (t : Fin (n.len + 1) → κ) :
    schemeCechTupleOpen f V (op n) t ≤
      schemeCechTupleOpen f U (op n) (fun j ↦ ρ (t j)) := by
  change (⨅ j, WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j ⁻¹ᵁ V (t j)) ≤
    ⨅ j, WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j ⁻¹ᵁ U (ρ (t j))
  apply le_iInf
  intro j
  exact (iInf_le _ j).trans (by intro x hx; exact hV (t j) hx)

/-- 同じ開の包含と元の各射影を脚に持つ、混合積の細分の射。 -/
def openFamilyCechRefinementMap (n : SimplexCategory) (t : Fin (n.len + 1) → κ) :
    finiteFamilyCechComponent (fun i ↦ (V i).ι ≫ f) n t ⟶
      finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n (fun j ↦ ρ (t j)) :=
  WidePullback.lift (WidePullback.base (fun j ↦ (V (t j)).ι ≫ f))
    (fun j ↦ WidePullback.π (fun j ↦ (V (t j)).ι ≫ f) j ≫ Y.homOfLE (hV (t j)))
    (fun j ↦ by
      rw [Category.assoc, ← Category.assoc (Y.homOfLE _), Scheme.homOfLE_ι,
        WidePullback.π_arrow])

/-- 同じ細分の射の射影は、元の開の包含を持つ。 -/
theorem openFamilyCechRefinementMap_π (n : SimplexCategory) (t : Fin (n.len + 1) → κ)
    (j : Fin (n.len + 1)) :
    openFamilyCechRefinementMap f U V ρ hV n t ≫
        WidePullback.π (fun j ↦ (U (ρ (t j))).ι ≫ f) j =
      WidePullback.π (fun j ↦ (V (t j)).ι ≫ f) j ≫ Y.homOfLE (hV (t j)) :=
  WidePullback.lift_π _ _ _ _ j

/-- 同じ細分の射は、元の基底の射を保つ。 -/
theorem openFamilyCechRefinementMap_base (n : SimplexCategory) (t : Fin (n.len + 1) → κ) :
    openFamilyCechRefinementMap f U V ρ hV n t ≫
        WidePullback.base (fun j ↦ (U (ρ (t j))).ι ≫ f) =
      WidePullback.base (fun j ↦ (V (t j)).ι ≫ f) :=
  WidePullback.lift_base _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 同じ細分の射は、元の nerve への入射を保つ。 -/
theorem openFamilyCechRefinementMap_inclusion (n : SimplexCategory)
    (t : Fin (n.len + 1) → κ) :
    openFamilyCechRefinementMap f U V ρ hV n t ≫
        openFamilyCechInclusion f U n (fun j ↦ ρ (t j)) =
      openFamilyCechInclusion f V n t := by
  apply WidePullback.hom_ext
  · intro j
    change (openFamilyCechRefinementMap f U V ρ hV n t ≫
      openFamilyCechInclusion f U n (fun j ↦ ρ (t j))) ≫
      WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j =
      openFamilyCechInclusion f V n t ≫ WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j
    rw [Category.assoc, openFamilyCechInclusion_π, ← Category.assoc,
      openFamilyCechRefinementMap_π, Category.assoc, Scheme.homOfLE_ι,
      openFamilyCechInclusion_π]
  · change (openFamilyCechRefinementMap f U V ρ hV n t ≫
      openFamilyCechInclusion f U n (fun j ↦ ρ (t j))) ≫
      WidePullback.base (fun _ : Fin (n.len + 1) ↦ f) =
      openFamilyCechInclusion f V n t ≫ WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)
    rw [Category.assoc, openFamilyCechInclusion_base, openFamilyCechRefinementMap_base,
      openFamilyCechInclusion_base]

set_option backward.isDefEq.respectTransparency false in
/-- 元のタプル開との標準同型は、同じ開の細分に自然。 -/
theorem openFamilyCechRefinementMap_iso (n : SimplexCategory) (t : Fin (n.len + 1) → κ) :
    openFamilyCechRefinementMap f U V ρ hV n t ≫
        (openFamilyCechIso f U n (fun j ↦ ρ (t j))).hom =
      (openFamilyCechIso f V n t).hom ≫
        ((Arrow.mk f).cechNerve.obj (op n)).homOfLE
          (openFamilyCechRefinementOpen_le f U V ρ hV n t) := by
  apply (cancel_mono (schemeCechTupleOpen f U (op n) (fun j ↦ ρ (t j))).ι).mp
  rw [Category.assoc, openFamilyCechIso_hom_fac, Category.assoc, Scheme.homOfLE_ι,
    openFamilyCechIso_hom_fac, openFamilyCechRefinementMap_inclusion]

end SerrePositivity.AlgebraicGeometry
