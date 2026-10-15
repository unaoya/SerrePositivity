module
public import SerrePositivity.DifferentialGraded.Derived.FreeSphereProjective
public import SerrePositivity.DifferentialGraded.Module.CoproductHom
public import SerrePositivity.DifferentialGraded.Module.Semifree.Basic
public import SerrePositivity.DifferentialGraded.Complexes.ProductAcyclic

/-! # 余積・自由sphere表示のhomotopically projective性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCoproduct_homotopicallyProjective {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    moduleHomotopicallyProjective A D (∐ M) := by
  intro N hN i
  exact (complexProduct_acyclic A (moduleCoproductHomFamily A D M N)
    (fun j => hM j N hN) i).of_iso (moduleCoproductHomIso A D M N).symm

lemma ModuleSphereFreePresentation.homotopicallyProjective {M : ModuleCategory A D}
    (S : ModuleSphereFreePresentation A D M) : moduleHomotopicallyProjective A D M := by
  let : Small.{u} S.Index := S.smallIndex
  exact moduleHomotopicallyProjective_of_iso A D S.iso.symm
    (moduleCoproduct_homotopicallyProjective A D _
      (fun t => freeSphere_homotopicallyProjective A D (S.object t) (S.degree t)))

lemma ModuleSemifreeFiltration.initial_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) : moduleHomotopicallyProjective A D (F.stage 0) :=
  F.initial.homotopicallyProjective A D

lemma ModuleSemifreeFiltration.quotient_homotopicallyProjective {M : ModuleCategory A D}
    (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleHomotopicallyProjective A D (F.quotient n) :=
  (F.quotientPresentation n).homotopicallyProjective A D

end SerrePositivity.DifferentialGraded
