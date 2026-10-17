module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence

/-! # 実際の主Perf制限の随伴shift・三角構造と包含の図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal1 :
    (perfectModuleInclusion A D Set.univ).Full :=
  inferInstanceAs ((modulePerfect A D).ι.Full)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal2 :
    (perfectModuleInclusion A D Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A D).ι.Faithful)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal3 :
    (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal4 :
    (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)
local instance moritaPerfectQuasiEquivalenceTrianglesLocal5 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal6 :
    (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal7 :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal8 :
    (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

@[instance_reducible]
def quasiEquivalencePerfectExtensionCommShift :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  Functor.CommShift.ofComp (quasiEquivalencePerfectExtensionInclusionIso A D E F) ℤ

@[instance_reducible]
def quasiEquivalencePerfectRestrictionCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ℤ

attribute [local instance] quasiEquivalencePerfectExtensionCommShift
  quasiEquivalencePerfectRestrictionCommShift

lemma quasiEquivalencePerfectExtensionInclusionCommShift :
    NatTrans.CommShift (quasiEquivalencePerfectExtensionInclusionIso A D E F).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (quasiEquivalencePerfectExtensionInclusionIso A D E F) ℤ

lemma quasiEquivalencePerfectRestrictionInclusionCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF).hom ℤ :=
  Functor.CommShift.ofComp_compatibility
    (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ℤ

attribute [local instance] quasiEquivalencePerfectExtensionInclusionCommShift
  quasiEquivalencePerfectRestrictionInclusionCommShift

lemma quasiEquivalencePerfectExtensionIsTriangulated :
    (quasiEquivalencePerfectExtension A D E F).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (quasiEquivalencePerfectExtensionInclusionIso A D E F)).2 inferInstance

lemma quasiEquivalencePerfectRestrictionIsTriangulated (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right
    (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF)).2 inferInstance

local instance moritaPerfectQuasiEquivalenceTrianglesLocal9 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).functor.CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceTrianglesLocal10 (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).inverse.CommShift ℤ :=
  quasiEquivalencePerfectRestrictionCommShift A D E F hF

lemma quasiEquivalencePerfectUnitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom ℤ := by
  let := dgDerivedExtensionUnit_commShift A D E F
  let I := perfectModuleInclusion A D Set.univ
  let J := perfectModuleInclusion A E Set.univ
  let L := dgDerivedExtension A D E F
  let R := dgDerivedRestriction A D E F
  let Lp := quasiEquivalencePerfectExtension A D E F
  let Rp := quasiEquivalencePerfectRestriction A D E F hF
  let α := quasiEquivalencePerfectExtensionInclusionIso A D E F
  let β := quasiEquivalencePerfectRestrictionInclusionIso A D E F hF
  have he : Functor.whiskerRight
      (quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom I =
      (Functor.leftUnitor I).hom ≫ (Functor.rightUnitor I).inv ≫
        Functor.whiskerLeft I (dgDerivedExtensionUnit A D E F) ≫
        (Functor.associator I L R).inv ≫ Functor.whiskerRight α.inv R ≫
        (Functor.associator Lp J R).hom ≫ Functor.whiskerLeft Lp β.inv ≫
        (Functor.associator Lp Rp I).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.associator_inv_app, Functor.associator_hom_app]
    change (dgDerivedExtensionUnit A D E F).app X.obj =
      𝟙 _ ≫ 𝟙 _ ≫ (dgDerivedExtensionUnit A D E F).app X.obj ≫
        𝟙 _ ≫ R.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm
  exact NatTrans.CommShift.of_comp_faithful (G := I) (h := by rw [he]; infer_instance)

lemma quasiEquivalencePerfectCommShift (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectEquivalence A D E F hF).CommShift ℤ :=
  Equivalence.CommShift.mk' _ _ (quasiEquivalencePerfectUnitCommShift A D E F hF)

lemma quasiEquivalencePerfectCounitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (quasiEquivalencePerfectEquivalence A D E F hF).counitIso.hom ℤ := by
  let := quasiEquivalencePerfectCommShift A D E F hF
  infer_instance

lemma quasiEquivalencePerfectIsTriangulated (hF : QuasiEquivalence F) :
    letI := quasiEquivalencePerfectCommShift A D E F hF
    (quasiEquivalencePerfectEquivalence A D E F hF).IsTriangulated := by
  let := quasiEquivalencePerfectCommShift A D E F hF
  exact Equivalence.IsTriangulated.mk' _ (quasiEquivalencePerfectExtensionIsTriangulated A D E F)

def quasiEquivalencePerfectExtensionTriangleIso :
    (quasiEquivalencePerfectExtension A D E F).mapTriangle ⋙
        (perfectModuleInclusion A E Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D Set.univ).mapTriangle ⋙
        (dgDerivedExtension A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalencePerfectExtensionInclusionIso A D E F) ≪≫
    Functor.mapTriangleCompIso _ _

def quasiEquivalencePerfectRestrictionTriangleIso (hF : QuasiEquivalence F) :
    (quasiEquivalencePerfectRestriction A D E F hF).mapTriangle ⋙
        (perfectModuleInclusion A D Set.univ).mapTriangle ≅
      (perfectModuleInclusion A E Set.univ).mapTriangle ⋙
        (dgDerivedRestriction A D E F).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (quasiEquivalencePerfectRestrictionInclusionIso A D E F hF) ≪≫
    Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
