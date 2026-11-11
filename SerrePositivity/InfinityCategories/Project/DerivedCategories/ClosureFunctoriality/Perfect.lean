module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.ClosureFunctor
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Derived.Functor

/-!
概要：実延長の代表化が、同じ導来 perfect 性を保つことを証明する。
方針：射影的源では恒等射影分解の計算同型で導来延長と実延長を比較する。
規約：標的代表への実 dg 同型をそのまま導来圏へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))
  (I : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D (dgModuleExtension R C D F) S T)

/-- D-3 preservesPerfect：射影的な実代表の perfect 性を保つ。 -/
lemma DGModuleStrictImage.preservesPerfect
    (hS : ∀ M, S M → moduleHomotopicallyProjective R C M)
    (M : {M // S M}) (hM : modulePerfect R C ((moduleToDerived R C).obj M.val)) :
    modulePerfect R D ((moduleToDerived R D).obj (I.obj M).val) := by
  let P := moduleIdentityProjectiveResolution R C M.val (hS M.val M.property)
  have h : modulePerfect R D
      ((moduleToDerived R D).obj ((dgModuleExtension R C D F).onClosed.obj M.val)) :=
    (modulePerfect R D).prop_of_iso (dgDerivedExtensionResolutionComputation R C D F P)
      (dgDerivedExtension_perfect R C D F hM)
  exact (modulePerfect R D).prop_of_iso
    ((moduleToDerived R D).mapIso (I.iso M)) h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
