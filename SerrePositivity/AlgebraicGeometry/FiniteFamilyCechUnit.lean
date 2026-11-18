module

public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechComponents
public import SerrePositivity.AlgebraicGeometry.FiniteFamilyFiberRecursion
public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerUnit

/-!
概要：同じ余積と Čech nerve の標準比較の零次は同型。
方針：元の単位の同型と余積の再添字付けを、同じ射影で照合する。
規約：同型へ置き換えるだけでなく、元の標準射の同型性を示す。
使われ方：有限余積とファイバー冪の分配の帰納の最初。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {ι : Type} {S : Scheme.{u}} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ余積射の nerve への標準比較の零次は同型。 -/
theorem finiteFamilyCechMap_zero_isIso : IsIso (finiteFamilyCechMap f (SimplexCategory.mk 0)) := by
  let e : (Fin 1 → ι) ≃ ι :=
    { toFun := fun t ↦ t 0
      invFun := fun i _ ↦ i
      left_inv := fun t ↦ funext (fun j ↦ congrArg t (Subsingleton.elim 0 j))
      right_inv := fun _ ↦ rfl }
  let E := CategoryTheory.Limits.Sigma.mapIso
      (fun t : Fin 1 → ι ↦ finiteFamilyFiberZeroIso (fun j ↦ f (t j))) ≪≫
    CategoryTheory.Limits.Sigma.reindex e Z
  let N := finiteFiberPowerZeroIso (CategoryTheory.Limits.Sigma.desc f)
  have he : finiteFamilyCechMap f (SimplexCategory.mk 0) ≫ N.hom = E.hom := by
    apply Sigma.hom_ext
    intro t
    change Sigma.ι (fun t : Fin 1 → ι ↦ finiteFamilyCechComponent f (SimplexCategory.mk 0) t) t ≫
      (finiteFamilyCechMap f (SimplexCategory.mk 0) ≫ N.hom) = _
    rw [← Category.assoc, finiteFamilyCechMap, Sigma.ι_comp_desc]
    change finiteFamilyCechInclusion f (SimplexCategory.mk 0) t ≫
      WidePullback.π (fun _ : Fin 1 ↦ CategoryTheory.Limits.Sigma.desc f) 0 = _
    rw [finiteFamilyCechInclusion_π]
    dsimp only [E]
    rw [Iso.trans_hom, ← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc]
    have hr := Sigma.ι_reindex_hom e Z t
    change Sigma.ι (fun t : Fin 1 → ι ↦ Z (t 0)) t ≫
      (CategoryTheory.Limits.Sigma.reindex e Z).hom = Sigma.ι Z (t 0) at hr
    rw [hr]
    rfl
  have h : finiteFamilyCechMap f (SimplexCategory.mk 0) = E.hom ≫ N.inv := by
    apply (cancel_mono N.hom).mp
    rw [Category.assoc, N.inv_hom_id, Category.comp_id, he]
  rw [h]
  infer_instance

end SerrePositivity.AlgebraicGeometry
