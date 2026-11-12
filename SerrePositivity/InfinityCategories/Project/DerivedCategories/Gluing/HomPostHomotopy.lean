module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-! 全 Hom の閉後合成は、元の H⁰ での同型を複体のホモトピー同型へ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- 複体値 dg 関手の H⁰ 作用を、同じ閉射の通常複体写像として回収する。 -/
lemma dgGluingComplexImageHomotopy_map (F : DGFunctor R C (Complex R))
    {x y : ClosedCategory R C} (f : x ⟶ y) :
    (F.onHomotopy ⋙ complexHomotopyComparison R).map ((toHomotopy R C).map f) =
      (Qh).map ((F.toComplexFunctor R).map f) := by
  have he : toHomotopy R C ⋙ (F.onHomotopy ⋙ complexHomotopyComparison R) =
      F.toComplexFunctor R ⋙ Qh := by
    rw [← CategoryTheory.Functor.assoc, DGFunctor.onHomotopy_fac,
      CategoryTheory.Functor.assoc, complexHomotopyComparison_fac]
    rfl
  exact eq_of_heq (CategoryTheory.Functor.hcongr_hom he f)

/-- 元の H⁰ 同型は、任意の複体値 dg 関手により通常の複体ホモトピー同型となる。 -/
lemma dgGluingComplexImageHomotopy_isIso (F : DGFunctor R C (Complex R))
    {x y : ClosedCategory R C} (f : x ⟶ y) (hf : IsIso ((toHomotopy R C).map f)) :
    IsIso ((Qh).map ((F.toComplexFunctor R).map f)) := by
  have := hf
  have hi : IsIso ((F.onHomotopy ⋙ complexHomotopyComparison R).map
      ((toHomotopy R C).map f)) := inferInstance
  rwa [dgGluingComplexImageHomotopy_map] at hi

/-- 全 Hom 後合成の斉次成分は、元の閉射の次数零元との豊穣順合成。 -/
lemma dgGluingHomPost_apply (x : C) {y z : ClosedCategory R C} (f : y ⟶ z)
    (n : ℤ) (t : GradedHom R x y n) :
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f).f n t =
      forward R t (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val (add_zero n) := by
  change (eComp (Complex R) x y z).f n
    (((homObject R C x y) ◁ ForgetEnrichment.homTo (Complex R) f).f n
      ((ρ_ (homObject R C x y)).inv.f n t)) = _
  rw [complexRightUnitor_inv_apply, SerrePositivity.DifferentialGraded.whiskerLeft_apply]
  rfl

/-- 共変代表 dg 加群の閉射作用は、元の全 Hom の閉後合成そのもの。 -/
lemma dgGluingLeftRepresentable_closed (x : C) {y z : ClosedCategory R C} (f : y ⟶ z) :
    ((leftRepresentable R x).toComplexFunctor R).map f =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f := by
  have he := DGFunctor.map_closedElement R (leftRepresentable R x) f
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hv := congrArg (fun h => h.v n n (add_zero n) t) he
  change leftAction R (leftRepresentable R x)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val t (add_zero n) =
      (((leftRepresentable R x).toComplexFunctor R).map f).f n t at hv
  rw [leftRepresentable_action] at hv
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hv
  erw [dgGluingHomPost_apply R C x f n t]
  exact hv.symm

/-- 全 Hom 後合成は、元の H⁰ 同型を通常複体のホモトピー同型へ送る。 -/
lemma dgGluingHomPost_isIso (x : C) {y z : ClosedCategory R C} (f : y ⟶ z)
    (hf : IsIso ((toHomotopy R C).map f)) :
    IsIso ((Qh).map (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) f)) := by
  have hi := dgGluingComplexImageHomotopy_isIso R C (leftRepresentable R x) f hf
  rwa [dgGluingLeftRepresentable_closed] at hi

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
