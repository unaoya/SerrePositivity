module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ModulePostAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.CommaPostHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Actions.HomConeBottomAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ClosedSquareHomotopy
/-! Hom の cone の比較ホモトピーを、元の閉射の同じ第三成分の評価と同定する。 -/
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

lemma dgGluingCommaThirdAction_module
    (A B C' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
    (f : ForgetEnrichment.of (Complex R) B ⟶ ForgetEnrichment.of (Complex R) C') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C' f =
    (modulePostcompositionMap R C A.replacement B.replacement (M.toFunctor.obj C'.source)).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedPrimitive R C D M B C' f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModulePostAction R C A.replacement B.replacement (M.toFunctor.obj C'.source)
    (ForgetEnrichment.homTo (Complex R) f) (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor B C')

variable (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y
local notation "C'" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Z
local notation "yZ" => dgYonedaIso R X.left (M.rightAt Z.right)
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition R C D M X Y Z f

lemma dgGluingHomConeHomotopy_yoneda :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy R C D M X Y Z f).comp (Cochain.ofHom (yZ).inv)
      (add_zero (-1)) =
    - (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComponentsIso R C D M X Y).hom ≫ biprod.snd)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C'
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) (zero_add (-1)) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_inl R C D M X Y
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso_primitive R C D M X Z
  have hk := dgHomMap_postcompose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (ForgetEnrichment.of (Complex R) X) f
  change k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Z).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) A)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f) at hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy_eq, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostcomposition_comparison]
  change (- (mappingCocone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)).comp
    ((Cochain.ofHom k).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Z) (zero_add (-1)))
      (zero_add (-1))).comp (Cochain.ofHom (yZ).inv) (add_zero (-1)) = _
  rw [Cochain.neg_comp, neg_inj]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [← hp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom k)
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Z).hom),
    ← Cochain.ofHom_comp, hk, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain
      (mappingCocone.inl (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y))
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M X Y).hom), hn,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaInl_post R D (RightModule R C) M.toFunctor A B C'
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma dgGluingHomConeHomotopy_action :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy R C D M X Y Z f =
    - (Cochain.ofHom biprod.fst).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M B C'
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f) X.left) (zero_add (-1)) := by
  calc
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy R C D M X Y Z f =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomConeHomotopy R C D M X Y Z f).comp (Cochain.ofHom (yZ).inv)
        (add_zero (-1))).comp (Cochain.ofHom (yZ).hom) (add_zero (-1)) := by
      simp only [Cochain.comp_assoc_of_third_is_zero_cochain,
        ← Cochain.ofHom_comp, Iso.inv_hom_id, Cochain.comp_id]
    _ = (- (Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComponentsIso R C D M X Y).hom ≫ biprod.snd)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C'
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f)) (zero_add (-1))).comp
        (Cochain.ofHom (yZ).hom) (add_zero (-1)) := by rw [dgGluingHomConeHomotopy_yoneda]
    _ = _ := by
      rw [dgGluingCommaThirdAction_module, Cochain.neg_comp,
        Cochain.comp_assoc_of_third_is_zero_cochain]
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingYonedaPostAction R C (representable R Y.left) (M.rightAt Z.right)
        (-1) X.left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedPrimitive R C D M B C'
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map f))]
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComponentsIso_hom]
      simp only [Category.assoc, biprod.lift_snd_assoc, yonedaHom,
        Iso.inv_hom_id, Category.comp_id]
      rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
