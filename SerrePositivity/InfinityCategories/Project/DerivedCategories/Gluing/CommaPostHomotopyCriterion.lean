module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPostCocone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomPostHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyBiproduct

/-! 閉 comma 射の両成分が H⁰ 同型なら、任意試験対象からの全 Hom 後合成はホモトピー同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- dg 関手は元の閉射の H⁰ 同型を、同じ像の閉射の H⁰ 同型へ送る。 -/
lemma dgGluingDGImageHomotopy_isIso {x y : ClosedCategory R C} (a : x ⟶ y)
    (ha : IsIso ((toHomotopy R C).map a)) :
    IsIso ((toHomotopy R E).map (F.onClosed.map a)) := by
  have := ha
  have hi : IsIso (F.onHomotopy.map ((toHomotopy R C).map a)) := inferInstance
  have he : F.onHomotopy.map ((toHomotopy R C).map a) =
      (toHomotopy R E).map (F.onClosed.map a) :=
    eq_of_heq (CategoryTheory.Functor.hcongr_hom (DGFunctor.onHomotopy_fac F) a)
  rwa [he] at hi

variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "a" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F)) f
local notation "b" => CategoryTheory.Functor.map
  (SerrePositivity.DifferentialGraded.DGFunctor.onClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F)) f

/-- 両成分の H⁰ 同型から、第三成分を含む同じ実 comma 後合成の K での同型が従う。 -/
lemma dgGluingCommaPostHomotopy_isIso
    (ha : IsIso ((toHomotopy R C).map a)) (hb : IsIso ((toHomotopy R E).map b)) :
    IsIso ((Qh).map
      (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)) := by
  have hI : IsIso ((toHomotopy R E).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R C E F Y Z f)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow_eq]
    exact dgGluingDGImageHomotopy_isIso R C E F a ha
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeExtract_isIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Z) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostComponents R C E F X Y Z f)
    (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X) f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_fst R C E F X Y Z f)
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingBiprodHomotopy_isIso R _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPost_isIso R C X.source a ha)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPost_isIso R E X.replacement b hb)
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_extractBottom]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPost_isIso R E X.replacement _ hI

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
