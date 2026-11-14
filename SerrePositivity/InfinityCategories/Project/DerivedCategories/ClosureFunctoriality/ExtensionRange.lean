module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.StrictRange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveClosureProperty
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorShiftIso
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued

/-!
概要：基底の実 dg 同型による像の被覆を、閉包の全段階へ伝播する。
方針：超限閉包の帰納原理へ実同型の飽和を入力する。
規約：基底に依存せず、全閉零次射の cone を扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R (RightModule R C) (RightModule R D))
  [hcolim : PreservesColimitsOfSize.{u, u} F.onClosed]
  (S : Set (ModuleCategory R D))
  (hzero : S (moduleZero R D))
  (hshift : ∀ M, S M → ∀ s : ℤ, S (M⟦s⟧))
  (hbinary : ∀ M N, S M → S N → S (M ⨿ N))
  (hcone : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f))
  (hcountable : ∀ M : ℕ → ModuleCategory R D, (∀ n, S (M n)) → S (∐ M))

include hcolim hzero hshift hbinary hcone hcountable in
lemma dgProjectiveClosureStage_extension_strictRange
    {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R C)
    (hB : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange R D S (F.onClosed.obj ((B.2 i).val)))
    (a : T) (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R C B a).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange R D S
      (F.onClosed.obj (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R C B a).2 i).val)) := by
  let : PreservesColimitsOfSize.{0, 0} F.onClosed :=
    preservesSmallestColimits_of_preservesColimits F.onClosed
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_property R C
    (fun M => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange R D S (F.onClosed.obj M))
    (F := B) (a := a) (i := i)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_iso R D S
      ((moduleZero_isZero R D).iso (F.onClosed.map_isZero (moduleZero_isZero R C)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_mem R D S hzero)
  · intro M hM s
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_iso R D S
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorShiftIso R C D F s (ForgetEnrichment.to (Complex R) M)).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_shift R D S hshift hM s)
  · intro M N hM hN
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_iso R D S (PreservesColimitPair.iso F.onClosed M N)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_binary R D S hbinary hM hN)
  · intro M N hM hN f
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_iso R D S (DGFunctor.moduleValuedConeIso R C D F f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_cone R D S hcone hM hN (F.onClosed.map f))
  · intro M hM
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_of_iso R D S (PreservesCoproduct.iso F.onClosed M).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgModuleStrictRange_countable R D S hcountable _ hM)
  · exact hB

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
