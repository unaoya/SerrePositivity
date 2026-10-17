module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Endomorphism.LargeHomBimodule

/-! # graphの左作用と共変representableの制限の一致

U14のYoneda成分比較を再利用し、graph tensorの作用と制限の向きを固定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma functorGraph_leftAt (e : E) :
    (functorGraph A D E F).leftAt e = F.comp (leftRepresentable A e) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (functorGraph A D E F).leftAt e) (G := F.comp (leftRepresentable A e)) (fun _ => rfl)
  intro d d'
  change ((F.map d d' ≫ yonedaHom A E (F.obj d) (F.obj d')) ≫
    moduleHomπ A E (representable A (F.obj d)) (representable A (F.obj d')) e) ≫
      eqToHom (by rfl) = F.map d d' ≫ (leftRepresentable A e).map (F.obj d) (F.obj d')
  rw [eqToHom_refl, Category.comp_id, Category.assoc, yonedaHom_π, endomorphismYonedaApp]

/-- 延長の各値は、共変representableをFに沿って制限した左加群とのtensor。 -/
def dgModuleExtensionValueIso (M : RightModule A D) (e : E) :
    ((dgModuleExtension A D E F).obj M).obj (op e) ≅
      BalancedTensor.obj A D M (F.comp (leftRepresentable A e)) :=
  eqToIso (congrArg (BalancedTensor.obj A D M) (functorGraph_leftAt A D E F e))

end SerrePositivity.DifferentialGraded
