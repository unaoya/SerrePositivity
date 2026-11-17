module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：非空の有限交叉の係数の同型から、全タプル Čech 複体の同型を得る。
方針：各次数のタプルの台は非空で、係数ごとの同型の積を取る。
規約：空の有限交叉の係数には仮定を置かない。
使われ方：nil 閉厚化の実際のアフィン交叉の係数を移す（計画 N01）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v

/-- 非空の台の係数が同型なら、全タプル Čech 複体の同じ写像も同型。 -/
theorem fullCechComplexMap_isIso_of_nonempty_support
    {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E)
    (hη : ∀ T : Finset ι, T.Nonempty → IsIso (η.app T)) :
    IsIso (fullCechComplexMap η) := by
  haveI : ∀ n : ℕ, IsIso ((fullCechComplexMap η).f n) := fun n ↦ by
    change IsIso (ModuleCat.ofHom (fullCechCochainsMap η (n + 1)))
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (Pi.map fun t : Fin (n + 1) → ι ↦ η.app (cechTupleSupport t))
    apply Function.Bijective.piMap
    intro t
    have ht : (cechTupleSupport t).Nonempty := by
      exact ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    letI := hη (cechTupleSupport t) ht
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact HomologicalComplex.Hom.isIso_of_components _

end SerrePositivity.AlgebraicGeometry
