module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.EnrichedClosedWhiskering

/-! 全 dg 自然な境界正方形から、同じ二成分を持つ実閉 comma 射を構成する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) Y.source)
  (b : ForgetEnrichment.of (Complex R) X.replacement ⟶
    ForgetEnrichment.of (Complex R) Y.replacement)
local notation "H" => homObject R E X.replacement (F.obj Y.source)

local notation "u" => (ForgetEnrichment.homTo (Complex R)
  (X := ForgetEnrichment.of (Complex R) X.replacement)
  (Y := ForgetEnrichment.of (Complex R) (F.obj Y.source))
  (X.augmentation ≫ F.onClosed.map a) : 𝟙_ (Complex R) ⟶ H)
local notation "v₀" => (ForgetEnrichment.homTo (Complex R)
  (X := ForgetEnrichment.of (Complex R) X.replacement)
  (Y := ForgetEnrichment.of (Complex R) (F.obj Y.source))
  (b ≫ Y.augmentation) : 𝟙_ (Complex R) ⟶ H)

/-- 閉射の単位からの全 Hom 写像は、同じ閉後合成を回収する。 -/
lemma dgGluingClosed_postcompose {U V W : ClosedCategory R E} (f : U ⟶ V) (g : V ⟶ W) :
    eHomEquiv (Complex R) f ≫ eHomWhiskerLeft (Complex R) U g =
      eHomEquiv (Complex R) (f ≫ g) := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerLeft]
  rw [rightUnitor_inv_naturality_assoc]
  simp only [Category.assoc, tensorHom_def, unitors_inv_equal]

/-- 閉二成分を差写像に入れると、同じ augmentation 正方形の閉射の差になる。 -/
lemma dgGluingCommaClosedDifference :
    biprod.lift (ForgetEnrichment.homTo (Complex R) a) (ForgetEnrichment.homTo (Complex R) b) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y =
    u - v₀ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, Preadditive.comp_sub]
  erw [Limits.biprod.lift_fst_assoc, Limits.biprod.lift_snd_assoc]
  have hF : ForgetEnrichment.homTo (Complex R) a ≫ F.map X.source Y.source =
      ForgetEnrichment.homTo (Complex R) (F.onClosed.map a) := by
    simp only [EnrichedFunctor.forget_map, ForgetEnrichment.homTo_homOf]
    rfl
  erw [← Category.assoc, hF]
  change (eHomEquiv (Complex R) (F.onClosed.map a) ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (F.onClosed.obj (.of (Complex R) Y.source)) : 𝟙_ (Complex R) ⟶ H) -
    (eHomEquiv (Complex R) b ≫ eHomWhiskerLeft (Complex R)
      (.of (Complex R) X.replacement) Y.augmentation : 𝟙_ (Complex R) ⟶ H) = _
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedClosed_precompose (Complex R) (ClosedCategory R E)
    X.augmentation (F.onClosed.map a), dgGluingClosed_postcompose R E b Y.augmentation]
  rfl

variable (h : boundaryRelation R E (b ≫ Y.augmentation) (X.augmentation ≫ F.onClosed.map a))

/-- 境界正方形の同じ単位からの次数 −1 の cochain。 -/
def dgGluingCommaBoundaryCochain : Cochain (𝟙_ (Complex R)) H (-1) :=
  Classical.choose ((unit_homotopy_iff H v₀ u).1 h)

/-- 選んだ cochain は、元の実差写像の境界式を満たす。 -/
lemma dgGluingCommaBoundaryCochain_boundary :
    δ (-1) 0 (dgGluingCommaBoundaryCochain R C E F X Y a b h) +
      Cochain.ofHom (Limits.biprod.lift (ForgetEnrichment.homTo (Complex R) a)
        (ForgetEnrichment.homTo (Complex R) b) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) = 0 := by
  have he := Classical.choose_spec ((unit_homotopy_iff H v₀ u).1 h)
  change (Cochain.ofHom v₀ : Cochain (𝟙_ (Complex R)) H 0) =
    δ (-1) 0 (dgGluingCommaBoundaryCochain R C E F X Y a b h) +
      (Cochain.ofHom u : Cochain (𝟙_ (Complex R)) H 0) at he
  rw [dgGluingCommaClosedDifference, Cochain.ofHom_sub]
  erw [← add_sub_assoc, ← he, sub_self]

/-- 同じ二つの閉射と境界正方形から得る、実 comma の閉射。 -/
def dgGluingCommaBoundaryLift : ForgetEnrichment.of (Complex R) X ⟶
    ForgetEnrichment.of (Complex R) Y :=
  ForgetEnrichment.homOf (Complex R)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X Y (𝟙_ (Complex R))
      (ForgetEnrichment.homTo (Complex R) a) (ForgetEnrichment.homTo (Complex R) b)
      (dgGluingCommaBoundaryCochain R C E F X Y a b h)
      (dgGluingCommaBoundaryCochain_boundary R C E F X Y a b h))

/-- 構成した閉 comma 射の source 射影は、指定した同じ閉射。 -/
lemma dgGluingCommaBoundaryLift_source : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R C E F).onClosed.map
    (dgGluingCommaBoundaryLift R C E F X Y a b h) = a := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) (dgGluingCommaBoundaryLift R C E F X Y a b h) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X Y) = a
  rw [dgGluingCommaBoundaryLift, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source, ForgetEnrichment.homOf_homTo]
/-- 構成した閉 comma 射の replacement 射影も、指定した同じ閉射。 -/
lemma dgGluingCommaBoundaryLift_replacement : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R C E F).onClosed.map
    (dgGluingCommaBoundaryLift R C E F X Y a b h) = b := by
  change ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) (dgGluingCommaBoundaryLift R C E F X Y a b h) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y) = b
  rw [dgGluingCommaBoundaryLift, ForgetEnrichment.homTo_homOf,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement, ForgetEnrichment.homOf_homTo]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
