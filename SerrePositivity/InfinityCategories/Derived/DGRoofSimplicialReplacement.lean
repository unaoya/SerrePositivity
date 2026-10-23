module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofRefinementVertices
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementEquivalence

/-! # 実屋根図式の simplicial replacement 比較

概要：共通宇宙の厳密分母添字で、元の屋根と固定商 Hom から商側屋根への全空間比較を作る。
方針：AsSmall で添字の Hom 宇宙を揃え、自然変換に F1 の simplicial replacement を適用する。
規約：元の対象・Hom の宇宙は同一視しない。使われ方：屋根の余極限比較への入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の厳密分母の反対添字の対象と Hom を共通宇宙へ置いた圏。 -/
abbrev DGCommonRoofIndex (P : Set D) (x : D) :=
  AsSmall.{max u v} ((DGClosedVerdierDenominators A D P x)ᵒᵖ)

/-- 共通宇宙の添字に沿う元の屋根図式。 -/
def dgCommonRoofOriginal (P : Set D) (x y : D) :
    DGCommonRoofIndex A D P x ⥤ SSet.{max u v} :=
  AsSmall.down ⋙ dgClosedVerdierRoofDiagram A D P x y

/-- 同じ共通宇宙の添字に沿う商側の屋根図式。 -/
def dgCommonRoofQuotient (P : Set D) (x y : D) :
    DGCommonRoofIndex A D P x ⥤ SSet.{max u v} :=
  AsSmall.down ⋙ dgQuotientRoofDiagram A D P x y

/-- 同じ共通宇宙の添字に沿う固定商 Hom の定値図式。 -/
def dgCommonRoofConstant (P : Set D) (x y : D) :
    DGCommonRoofIndex A D P x ⥤ SSet.{max u v} :=
  AsSmall.down ⋙ dgQuotientRoofConstant A D P x y

/-- 共通宇宙の元の屋根図式から商側図式への自然比較。 -/
def dgCommonRoofComparison (P : Set D) (x y : D) :
    dgCommonRoofOriginal A D P x y ⟶ dgCommonRoofQuotient A D P x y :=
  Functor.whiskerLeft AsSmall.down (dgQuotientRoofComparison A D P x y)

/-- 共通宇宙の固定商 Hom 図式から商側屋根図式への自然比較。 -/
def dgCommonRoofConstantComparison (P : Set D) (x y : D) :
    dgCommonRoofConstant A D P x y ⟶ dgCommonRoofQuotient A D P x y :=
  Functor.whiskerLeft AsSmall.down (dgQuotientRoofConstantComparison A D P x y)

/-- 元の実屋根比較が誘導する simplicial replacement 全空間の写像。 -/
def dgRoofReplacementComparison (P : Set D) (x y : D) :
    simplicialReplacement (dgCommonRoofOriginal A D P x y) ⟶
      simplicialReplacement (dgCommonRoofQuotient A D P x y) :=
  simplicialReplacementMap (dgCommonRoofComparison A D P x y)

/-- 固定商 Hom 比較が誘導する simplicial replacement 全空間の写像。 -/
def dgRoofReplacementConstantComparison (P : Set D) (x y : D) :
    simplicialReplacement (dgCommonRoofConstant A D P x y) ⟶
      simplicialReplacement (dgCommonRoofQuotient A D P x y) :=
  simplicialReplacementMap (dgCommonRoofConstantComparison A D P x y)

/-- 元の屋根の全空間比較は、厳密分母添字の射列を厳密に保つ。 -/
lemma dgRoofReplacementComparison_projection (P : Set D) (x y : D) :
    dgRoofReplacementComparison A D P x y ≫
      simplicialReplacementProjection (dgCommonRoofQuotient A D P x y) =
        simplicialReplacementProjection (dgCommonRoofOriginal A D P x y) :=
  simplicialReplacementMap_projection _

/-- 固定商 Hom の全空間比較も、同じ厳密分母添字の射列を厳密に保つ。 -/
lemma dgRoofReplacementConstantComparison_projection (P : Set D) (x y : D) :
    dgRoofReplacementConstantComparison A D P x y ≫
      simplicialReplacementProjection (dgCommonRoofQuotient A D P x y) =
        simplicialReplacementProjection (dgCommonRoofConstant A D P x y) :=
  simplicialReplacementMap_projection _

/-- 固定商 Hom 側の全空間比較は、任意の標的に対する前合成同値。 -/
lemma dgRoofReplacementConstantComparison_isPrecompositionEquivalence
    [IsDGPretriangulated A D] (P : Set D) (hP : localKFlat A D P) (x y : D) :
    IsPrecompositionEquivalence (dgRoofReplacementConstantComparison A D P x y) := by
  have (c : DGCommonRoofIndex A D P x) :
      KanComplex ((dgCommonRoofConstant A D P x y).obj c) :=
    inferInstanceAs (KanComplex (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj y)))
  have (c : DGCommonRoofIndex A D P x) :
      KanComplex ((dgCommonRoofQuotient A D P x y).obj c) :=
    inferInstanceAs (KanComplex (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A)
        ((AsSmall.down.obj c).unop.obj.left))) ((inclusion A D P).obj y)))
  apply simplicialReplacementMap_isPrecompositionEquivalence
  intro c
  have : KanComplex ((dgQuotientRoofConstant A D P x y).obj (AsSmall.down.obj c)) :=
    inferInstanceAs (KanComplex (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj y)))
  have : KanComplex ((dgQuotientRoofDiagram A D P x y).obj (AsSmall.down.obj c)) :=
    inferInstanceAs (KanComplex (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A)
        ((AsSmall.down.obj c).unop.obj.left))) ((inclusion A D P).obj y)))
  exact (dgQuotientRoofConstantComparison_app_equivalence A D P hP x y
    (AsSmall.down.obj c).unop).isQCatEquivalence

end SerrePositivity.InfinityCategories
