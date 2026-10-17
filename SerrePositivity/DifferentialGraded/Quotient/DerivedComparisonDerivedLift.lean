module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonHomNormalization
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtension
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles

/-! # 実際の導来延長の Verdier 因子化と代表対象への射写像の全単射性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance (S : Set D) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).CommShift ℤ :=
  dgDerivedExtensionCommShift A D _ _
local instance (S : Set D) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D _ _

instance derivedComparisonFromTriaCommShift (S : Set D) :
    (derivedComparisonFromTria A D S).CommShift ℤ := by
  dsimp [derivedComparisonFromTria]
  infer_instance
instance derivedComparisonFromTriaIsTriangulated (S : Set D) :
    (derivedComparisonFromTria A D S).IsTriangulated := by
  dsimp [derivedComparisonFromTria]
  infer_instance

lemma derivedComparisonFromTria_inverts (S : Set D) :
    (triaImage A D S).trW.IsInvertedBy (derivedComparisonFromTria A D S) := by
  intro X Y f hf
  apply (triangulatedKernel_trW_iff (derivedComparisonFromTria A D S) f).1
  exact (triaImage A D S).trW_monotone
    (fun X hX => derivedComparisonFromTria_kills A D S X hX) _ hf

/-- 普通の加群の導来延長を、指定 Verdier 商に沿って因子化した関手。 -/
def derivedQuotientLift (S : Set D) :
    TriaQuotient A D S ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  Localization.lift (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

def derivedQuotientLiftFactors (S : Set D) :
    triaQuotient A D S ⋙ derivedQuotientLift A D S ≅ derivedComparisonFromTria A D S :=
  Localization.fac (derivedComparisonFromTria A D S)
    (derivedComparisonFromTria_inverts A D S) (triaQuotient A D S)

/-- 因子化同型と代表対象の計算同型で移した、因子化関手の実際の射写像。 -/
def derivedQuotientLiftRepresentableMap (S : Set D) (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    (derivedComparisonFromTria A D S).obj X ⟶
      (moduleToDerived A (QuotientObject D S)).obj
        (ForgetEnrichment.of (Complex A) (representable A (⟨z⟩ : QuotientObject D S))) :=
  (derivedQuotientLiftFactors A D S).inv.app X ≫ (derivedQuotientLift A D S).map f ≫
    (derivedQuotientLiftFactors A D S).hom.app (triaRepresentable A D z) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom

lemma derivedQuotientLiftRepresentableMap_map (S : Set D) (z : D)
    {X : TriaCategory A D} (f : X ⟶ triaRepresentable A D z) :
    derivedQuotientLiftRepresentableMap A D S z X ((triaQuotient A D S).map f) =
      (derivedComparisonFromTria A D S).map f ≫
        (derivedExtensionRepresentableUnitIso A D (QuotientObject D S)
          (inclusion A D S) z).hom := by
  have he := congrArg (fun t => t ≫
    (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom)
    (NatIso.naturality_1 (derivedQuotientLiftFactors A D S) f)
  simpa only [derivedQuotientLiftRepresentableMap, Category.assoc, Functor.comp_map] using he


lemma derivedQuotientLiftRepresentableMap_precomp (S : Set D) (z : D)
    {X Y : TriaCategory A D} (s : X ⟶ Y)
    (f : (triaQuotient A D S).obj Y ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    derivedQuotientLiftRepresentableMap A D S z X ((triaQuotient A D S).map s ≫ f) =
      (derivedComparisonFromTria A D S).map s ≫
        derivedQuotientLiftRepresentableMap A D S z Y f := by
  unfold derivedQuotientLiftRepresentableMap
  rw [CategoryTheory.Functor.map_comp]
  have hn := (derivedQuotientLiftFactors A D S).inv.naturality s
  change (derivedComparisonFromTria A D S).map s ≫
      (derivedQuotientLiftFactors A D S).inv.app Y =
    (derivedQuotientLiftFactors A D S).inv.app X ≫
      (derivedQuotientLift A D S).map ((triaQuotient A D S).map s) at hn
  have he := congrArg (fun t => t ≫ (derivedQuotientLift A D S).map f ≫
    (derivedQuotientLiftFactors A D S).hom.app (triaRepresentable A D z) ≫
      (derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z).hom) hn
  simpa only [Category.assoc] using he.symm


/-- 右分数表示により、元の射上での一致は指定 Verdier 商の全ての射へ延びる。 -/
lemma derivedQuotientLiftRepresentableMap_eq (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D)
    (f : (triaQuotient A D S).obj X ⟶
      (triaQuotient A D S).obj (triaRepresentable A D z)) :
    derivedQuotientLiftRepresentableMap A D S z X f =
      quotientDerivedRepresentableHomEquiv A D S h z X f := by
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction
    (triaQuotient A D S) (triaImage A D S).trW f
  have he : (triaQuotient A D S).map φ.s ≫ f = (triaQuotient A D S).map φ.f := by
    rw [hφ, MorphismProperty.RightFraction.map_s_comp_map]
  have : IsIso ((derivedComparisonFromTria A D S).map φ.s) :=
    derivedComparisonFromTria_inverts A D S φ.s φ.hs
  apply (cancel_epi ((derivedComparisonFromTria A D S).map φ.s)).1
  refine (derivedQuotientLiftRepresentableMap_precomp A D S z φ.s f).symm.trans ?_
  refine Eq.trans ?_ (quotientDerivedRepresentableHomEquiv_precomp A D S h z φ.s f)
  rw [he, derivedQuotientLiftRepresentableMap_map]
  exact (quotientDerivedRepresentableHomEquiv_map A D S h z φ.f).symm


lemma derivedQuotientLiftRepresentableMap_bijective (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    Function.Bijective (derivedQuotientLiftRepresentableMap A D S z X) := by
  have he : derivedQuotientLiftRepresentableMap A D S z X =
      quotientDerivedRepresentableHomEquiv A D S h z X := by
    funext f
    exact derivedQuotientLiftRepresentableMap_eq A D S h z X f
  rw [he]
  exact (quotientDerivedRepresentableHomEquiv A D S h z X).bijective

/-- 代表対象を終域とする、因子化関手そのものの射写像は全単射。 -/
lemma derivedQuotientLift_map_bijective_representable (S : Set D) (h : localKFlat A D S)
    (z : D) (X : TriaCategory A D) :
    Function.Bijective ((derivedQuotientLift A D S).map
      (X := (triaQuotient A D S).obj X)
      (Y := (triaQuotient A D S).obj (triaRepresentable A D z))) := by
  let eX := (derivedQuotientLiftFactors A D S).app X
  let eZ := (derivedQuotientLiftFactors A D S).app (triaRepresentable A D z) ≪≫
    derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z
  apply (Function.Bijective.of_comp_iff' (Iso.homCongr eX eZ).bijective _).1
  exact derivedQuotientLiftRepresentableMap_bijective A D S h z X

end SerrePositivity.DifferentialGraded.DGQuotient
