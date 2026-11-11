module
public import SerrePositivity.KST.SConstruction.DGStandardClosedComparison
public import SerrePositivity.KST.SConstruction.DGStandardCoherentMap
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EnrichedHomotopy

/-! # 全 Hom 閉零同型の標準 coherent nerve への移送
概要：標準 DK へ移した閉零比較は、元の成分を持つ実関手同型を与える。
方針：零単体から同じ閉零射を回収し、実閉零逆射で全成分の可逆性を示す。
規約：源に Small を仮定しない。使われ方：実 Perf 延長とラベル作用の完全性の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 標準閉定数の零単体を評価すると同じ元の閉零元を回収する。 -/
lemma dgStandardConstant_zeroEval {x y : E} (z : zeroCycles (homObject A E x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant z 0) = z := by
  apply Subtype.ext
  have hs : (Finset.univ : Finset (Fin 1)) = {0} := by decide
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant z 0).val.component Finset.univ 0
    Finset.univ_nonempty (by simp) = z.val
  simpa only [← hs] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_singleton z (0 : Fin 1)

/-- 閉零射の標準定数族の零単体は、同じ元の閉零射の標準頂点。 -/
lemma dgStandardClosedMap_vertex {x y : E}
    (a : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    (dgStandardClosedMap a).app (Opposite.op ⦋0⦌) PUnit.unit =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := A) (D := E) _ _ a := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := A) (D := E) x y).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x y (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv A E _ _ a) 0) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := A) (D := E) x y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := A) (D := E) x y).symm (closedHomEquiv A E _ _ a))
  rw [LinearEquiv.apply_symm_apply]
  exact dgStandardConstant_zeroEval _

/-- 元の閉零射の標準単位射から、同じ通常の閉零射を回収する。 -/
lemma dgStandardClosedMap_hom {x y : E}
    (a : ForgetEnrichment.of (Complex A) x ⟶ ForgetEnrichment.of (Complex A) y) :
    (SimplicialCategory.homEquiv'
      (ForgetEnrichment.of (Complex A) x) (ForgetEnrichment.of (Complex A) y)).symm
        ((dgStandardClosedMap a).app (Opposite.op ⦋0⦌) PUnit.unit) = a := by
  apply (SimplicialCategory.homEquiv'
    (ForgetEnrichment.of (Complex A) x) (ForgetEnrichment.of (Complex A) y)).injective
  rw [Equiv.apply_symm_apply, dgStandardClosedMap_vertex]
  change _ = (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm _)
  rw [Equiv.apply_symm_apply]

variable (F G : DGFunctor A D E)
  (a : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
    ForgetEnrichment.of (Complex A) (G.obj x))
  (h : ∀ x y : D, F.map x y ≫
    eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (a y) =
    G.map x y ≫ eHomWhiskerRight (Complex A) (a x)
      (ForgetEnrichment.of (Complex A) (G.obj y)))

/-- 標準 DK 比較から回収する成分は、選び直していない元の閉零射。 -/
lemma dgStandardClosedComparison_component (X : ClosedCategory A D) :
    Spectra.StrictEnrichedTransformation.componentHom
      (dgStandardEnrichedFunctor F) (dgStandardEnrichedFunctor G)
      (dgStandardClosedComparison F G a h) X = a (ForgetEnrichment.to (Complex A) X) :=
  dgStandardClosedMap_hom (a (ForgetEnrichment.to (Complex A) X))

/-- 全 Hom 上で自然な閉零同型族は、同じ標準 coherent 関手の実同型を与える。 -/
def dgStandardClosedComparisonIso
    (e : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ≅
      ForgetEnrichment.of (Complex A) (G.obj x))
    (he : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (e y).hom =
      G.map x y ≫ eHomWhiskerRight (Complex A) (e x).hom
        (ForgetEnrichment.of (Complex A) (G.obj y))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgStandardCoherentMap F) (dgStandardCoherentMap G) :=
  Spectra.StrictEnrichedTransformation.functorIso
    (dgStandardEnrichedFunctor F) (dgStandardEnrichedFunctor G)
    (dgStandardClosedComparison F G (fun x => (e x).hom) he) (by
      intro X
      rw [dgStandardClosedComparison_component]
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse _
        (e (ForgetEnrichment.to (Complex A) X)).inv
      · rw [Iso.hom_inv_id]
      · rw [Iso.inv_hom_id])

end SerrePositivity.KST.SConstruction
