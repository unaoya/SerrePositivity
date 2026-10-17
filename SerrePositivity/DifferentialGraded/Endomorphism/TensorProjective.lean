module
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion
public import SerrePositivity.DifferentialGraded.Endomorphism.HomotopyAdjunction
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHom

/-! # 指定射影的dg加群とのtensorによるホモトピー射影性の保存

主K上の随伴とHomの擬同型保存から、coyonedaによる判定を用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Eの射影性の下で、主K上のHom関手も指定擬同型を保つ。 -/
lemma endomorphismHomotopyHom_quasiIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) (hf : moduleHomotopyQuasiIso A D f) :
    moduleHomotopyQuasiIso A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onHomotopy.map f) := by
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  change moduleHomotopyQuasiIso A (EndomorphismObject E)
    ((moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map g))
  exact (moduleHomotopyQuasiIso_map_iff A (EndomorphismObject E) _).mpr
    (endomorphismModuleHom_quasiIso A D E hE g ((moduleHomotopyQuasiIso_map_iff A D g).mp hf))

/-- Eがホモトピー射影的なら、再構成tensorは射影的右End(E)加群を射影的右D加群へ送る。 -/
lemma endomorphismModuleTensor_homotopicallyProjective
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {P : ModuleCategory A (EndomorphismObject E)}
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P) :
    moduleHomotopicallyProjective A D ((endomorphismModuleTensor A D E).onClosed.obj P) := by
  apply moduleHomotopicallyProjective_of_coyoneda_inverts A D
  intro X Y f hf
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  let adj := endomorphismHomotopyAdjunction A D E
  let Rf := (endomorphismModuleHom A D E).onHomotopy.map f
  have hRf := endomorphismHomotopyHom_quasiIso A D E hE f hf
  have hpost := (CategoryTheory.isIso_iff_bijective _).mp
    (moduleHomotopicallyProjective_coyoneda_inverts A (EndomorphismObject E) hP Rf hRf)
  change Function.Bijective (fun s :
      (endomorphismModuleTensor A D E).onHomotopy.obj
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ⟶ X => s ≫ f)
  let eX := adj.homEquiv ((moduleToHomotopy A (EndomorphismObject E)).obj P) X
  let eY := adj.homEquiv ((moduleToHomotopy A (EndomorphismObject E)).obj P) Y
  have heq : (fun s :
      (endomorphismModuleTensor A D E).onHomotopy.obj
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ⟶ X => s ≫ f) =
      fun s => eY.symm (eX s ≫ Rf) := by
    funext s
    apply eY.injective
    rw [Equiv.apply_symm_apply]
    exact adj.homEquiv_naturality_right s f
  rw [heq]
  exact eY.symm.bijective.comp (hpost.comp eX.bijective)

end SerrePositivity.DifferentialGraded
