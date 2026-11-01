module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGGraphCompositionInputLeft
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedNaturality
/-!
概要：代表加群の実延長比較の全 Hom 自然性を、同じ閉射の可換式として公開する。
方針：既存の全次数自然性に、閉射による前合成を適用する。
規約：元の代表同型と dg 関手の射作用を変更しない。
使われ方：c′ のコード内閉射から、実延長した代表加群間閉射を精密化する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

lemma dgModuleExtensionRepresentableIso_closed_naturality
    {x y : ClosedCategory R D} (f : x ⟶ y) :
    (dgModuleExtension R D E F).onClosed.map ((dgYoneda R D).onClosed.map f) ≫
      (dgModuleExtensionRepresentableIso R D E F (ForgetEnrichment.to (Complex R) y)).hom =
    (dgModuleExtensionRepresentableIso R D E F (ForgetEnrichment.to (Complex R) x)).hom ≫
      (dgYoneda R E).onClosed.map (F.onClosed.map f) := by
  exact dgFunctorClosedComparison_naturality R
    ((dgYoneda R D).comp (dgModuleExtension R D E F)) (F.comp (dgYoneda R E))
    (fun x => (dgModuleExtensionRepresentableIso R D E F x).hom)
    (dgModuleExtensionRepresentableIso_naturality R D E F) f

end SerrePositivity.DifferentialGraded
