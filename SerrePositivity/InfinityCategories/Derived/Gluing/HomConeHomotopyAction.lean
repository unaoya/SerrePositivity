module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModulePostAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaPostHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomConeBottomAction
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedSquareHomotopy
/-! Hom の cone の比較ホモトピーを、元の閉射の同じ第三成分の評価と同定する。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingCommaThirdAction_module
    (A B C' : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
    (f : ForgetEnrichment.of (Complex R) B ⟶ ForgetEnrichment.of (Complex R) C') :
    dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C' f =
    (modulePostcompositionMap R C A.replacement B.replacement (M.toFunctor.obj C'.source)).f (-1)
      (dgGluingCommaClosedPrimitive R C D M B C' f) :=
  dgGluingModulePostAction R C A.replacement B.replacement (M.toFunctor.obj C'.source)
    (ForgetEnrichment.homTo (Complex R) f) (-1)
      (dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor B C')

variable (X Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "A" => dgGluingCommaObject R C D M X
local notation "B" => dgGluingCommaObject R C D M Y
local notation "C'" => dgGluingCommaObject R C D M Z
local notation "yZ" => dgYonedaIso R X.left (M.rightAt Z.right)
local notation "k" => dgGluingPostcomposition R C D M X Y Z f

lemma dgGluingHomConeHomotopy_yoneda :
    (dgGluingHomConeHomotopy R C D M X Y Z f).comp (Cochain.ofHom (yZ).inv)
      (add_zero (-1)) =
    - (Cochain.ofHom ((dgGluingHomComponentsIso R C D M X Y).hom ≫ biprod.snd)).comp
      (dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C'
        ((dgGluingToComma R C D M).onClosed.map f)) (zero_add (-1)) := by
  have hn := dgGluingHomRepresentableIso_inl R C D M X Y
  have hp := dgGluingHomRepresentableIso_primitive R C D M X Z
  have hk := dgHomMap_postcompose (dgGluingToComma R C D M)
    (ForgetEnrichment.of (Complex R) X) f
  change k ≫ (dgGluingHomRepresentableIso R C D M X Z).hom =
    (dgGluingHomRepresentableIso R C D M X Y).hom ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) A)
        ((dgGluingToComma R C D M).onClosed.map f) at hk
  rw [dgGluingHomConeHomotopy_eq, ← dgGluingPostcomposition_comparison]
  change (- (mappingCocone.inl (dgGluingDifference R C D M X Y)).comp
    ((Cochain.ofHom k).comp (dgGluingHomPrimitive R C D M X Z) (zero_add (-1)))
      (zero_add (-1))).comp (Cochain.ofHom (yZ).inv) (add_zero (-1)) = _
  rw [Cochain.neg_comp, neg_inj]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain]
  rw [← hp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom k)
    (Cochain.ofHom (dgGluingHomRepresentableIso R C D M X Z).hom),
    ← Cochain.ofHom_comp, hk, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain
      (mappingCocone.inl (dgGluingDifference R C D M X Y))
      (Cochain.ofHom (dgGluingHomRepresentableIso R C D M X Y).hom), hn,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [dgGluingCommaInl_post R D (RightModule R C) M.toFunctor A B C'
    ((dgGluingToComma R C D M).onClosed.map f)]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma dgGluingHomConeHomotopy_action :
    dgGluingHomConeHomotopy R C D M X Y Z f =
    - (Cochain.ofHom biprod.fst).comp
      (dgGluingCommaClosedSquareHomotopy R C D M B C'
        ((dgGluingToComma R C D M).onClosed.map f) X.left) (zero_add (-1)) := by
  calc
    dgGluingHomConeHomotopy R C D M X Y Z f =
      ((dgGluingHomConeHomotopy R C D M X Y Z f).comp (Cochain.ofHom (yZ).inv)
        (add_zero (-1))).comp (Cochain.ofHom (yZ).hom) (add_zero (-1)) := by
      simp only [Cochain.comp_assoc_of_third_is_zero_cochain,
        ← Cochain.ofHom_comp, Iso.inv_hom_id, Cochain.comp_id]
    _ = (- (Cochain.ofHom ((dgGluingHomComponentsIso R C D M X Y).hom ≫ biprod.snd)).comp
      (dgGluingCommaThirdAction R D (RightModule R C) M.toFunctor A B C'
        ((dgGluingToComma R C D M).onClosed.map f)) (zero_add (-1))).comp
        (Cochain.ofHom (yZ).hom) (add_zero (-1)) := by rw [dgGluingHomConeHomotopy_yoneda]
    _ = _ := by
      rw [dgGluingCommaThirdAction_module, Cochain.neg_comp,
        Cochain.comp_assoc_of_third_is_zero_cochain]
      erw [dgGluingYonedaPostAction R C (representable R Y.left) (M.rightAt Z.right)
        (-1) X.left (dgGluingCommaClosedPrimitive R C D M B C'
          ((dgGluingToComma R C D M).onClosed.map f))]
      rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
        dgGluingHomComponentsIso_hom]
      simp only [Category.assoc, biprod.lift_snd_assoc, yonedaHom,
        Iso.inv_hom_id, Category.comp_id]
      rfl

end SerrePositivity.InfinityCategories
