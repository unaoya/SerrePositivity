module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.InclusionTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaPostBottom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomConeComparison
/-! Hom の cone から回収した下辺を、元の右成分に沿う双加群の実作用と同定する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y
local notation "C'" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z
local notation "yY" => dgYonedaIso R X.left (M.rightAt Y.right)
local notation "yZ" => dgYonedaIso R X.left (M.rightAt Z.right)
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f

lemma dgGluingHomConeBottom_yoneda :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f ≫ (yZ).inv =
      (yY).inv ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (A).replacement)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R D (RightModule R C) M.toFunctor B C'
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) := by
  apply Cochain.ofHom_injective
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_inr R C D M X Y
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive R C D M X Z
  have hk := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (ForgetEnrichment.of (Complex R) X) f
  change k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Z).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) A)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f) at hk
  rw [Cochain.ofHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom_cochain,
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_comparison]
  change (((mappingCocone.inr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)).val).comp
    ((Cochain.ofHom k).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z) (zero_add (-1)))
    (add_neg_cancel 1)).comp (Cochain.ofHom (yZ).inv) (add_zero 0) = _
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [← hp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, hk,
    Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, hn]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPost_bottom R D (RightModule R C) M.toFunctor A B C'
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)]
  rw [← Cochain.ofHom_comp]

lemma dgGluingYoneda_postcompose (c : C) {U V : RightModule R C}
    (g : ForgetEnrichment.of (Complex R) U ⟶ ForgetEnrichment.of (Complex R) V) :
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R c)) g ≫
        (dgYonedaIso R c V).hom =
      (dgYonedaIso R c U).hom ≫ (moduleEvaluation R C c).map g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (dgYonedaIso R c V).hom.f n
    ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (representable R c)) g).f n z) =
    ((moduleEvaluation R C c).map g).f n ((dgYonedaIso R c U).hom.f n z)
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  change (((eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R c)) g ≫
      moduleHomπ R C (representable R c) V c).f n z).v 0 n (zero_add n)
        (unitElement R c).val) = _
  erw [moduleHomWhiskerLeft_π R C
    (M := ForgetEnrichment.of (Complex R) (representable R c)) g c]
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  change (((moduleHomπ R C (representable R c) U c).f n z).comp
    (Cochain.ofHom ((moduleEvaluation R C c).map g)) (add_zero n)).v 0 n (zero_add n)
    (unitElement R c).val = _
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

lemma dgGluingHomConeBottom_action : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f =
    (moduleEvaluation R C X.left).map
      (M.toFunctor.onClosed.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).onClosed.map f)) := by
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaPostImageArrow R D (RightModule R C) M.toFunctor B C'
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)
  have hy := dgGluingYoneda_postcompose R C X.left g
  change eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (representable R X.left)) g ≫ (yZ).hom =
      (yY).hom ≫ (moduleEvaluation R C X.left).map g at hy
  calc
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeBottom R C D M X Y Z f ≫ (yZ).inv) ≫ (yZ).hom := by simp
    _ = ((yY).inv ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left)) g) ≫ (yZ).hom := by
      rw [dgGluingHomConeBottom_yoneda]
      rfl
    _ = (yY).inv ≫ (yY).hom ≫ (moduleEvaluation R C X.left).map g := by
      rw [Category.assoc, hy]
    _ = _ := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
