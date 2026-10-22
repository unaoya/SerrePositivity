module
public import SerrePositivity.KST.Fibration.DGKSBoundaryPi
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant

/-! # 元の S• 境界商と固定 BF 正段の全 coherent 比較

全 Hom 上の元の自然性を実区間族へ写し、同じ元の相対四角形へ制限する。
辺の自然性だけから高次の比較を推論しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 固定 BF の元の全正段を、同じ全 Hom 作用のまま Kan 全部分圏に束ねる。 -/
def dgKPositiveKanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} where
  obj P := ⟨((presentedPerfectDGBFPositiveStage A r).functor.obj P).obj,
    (presentedPerfectDGBFPositiveStage A r).kan P⟩
  map P Q := (presentedPerfectDGBFPositiveStage A r).functor.map P Q
  map_id P := (presentedPerfectDGBFPositiveStage A r).functor.map_id P
  map_comp P Q R := (presentedPerfectDGBFPositiveStage A r).functor.map_comp P Q R

/-- 元の境界商 Kan 値から固定 BF 正段への、同じ元の通常成分。 -/
def dgKSBoundaryPositiveComponent (r : ℕ) (P : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj P ⟶
      (dgKPositiveKanEnrichedFunctor A r).obj P :=
  ObjectProperty.homMk ((presentedPerfectDGBFPositiveStage A r).comparison P)

/-- 全 native Hom の自然性から、同じ元の成分を持つ厳密豊穣自然変換を作る。 -/
def dgKSBoundaryPositiveTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGBoundaryKanEnrichedFunctor A r)
      (dgKPositiveKanEnrichedFunctor A r) :=
  strictSimplicialTransformationOfWhisker _ _ (dgKSBoundaryPositiveComponent A r)
    (fun P Q => (presentedPerfectDGBFPositiveStage A r).naturality P Q)

/-- 境界商と固定正段を結ぶ、全高次単体を保持した元の比較の区間族。 -/
def dgKSBoundaryPositiveHomotopy (r : ℕ) :
    SSet.Homotopy (presentedPerfectDGBoundaryKanInfinityFunctor A r)
      (coherentNerveMap (dgKPositiveKanEnrichedFunctor A r)) :=
  StrictEnrichedTransformation.homotopy _ _ (dgKSBoundaryPositiveTransformation A r)

/-- 全 coherent 比較の各頂点の辺は、元の前向き弱比較の辺そのもの。 -/
theorem dgKSBoundaryPositiveHomotopy_component (r : ℕ) (P : PerfDGInput.{u, v} A) :
    (simplicialHomotopyVertexEdge (dgKSBoundaryPositiveHomotopy A r)
      (coherentNerveVertex P)).edge =
      (coherentNerveEdge (dgKSBoundaryPositiveComponent A r P)).edge := by
  rw [dgKSBoundaryPositiveHomotopy, StrictEnrichedTransformation.homotopy_component]
  rw [strictSimplicialTransformation_componentHom _ _ _ P
    (dgKSBoundaryPositiveComponent A r P) rfl]

/-- 元の同じ全入力比較は、関手 ∞ 圏内の自然同型である。 -/
def dgKSBoundaryPositiveIso (r : ℕ) :
    FunctorIso (presentedPerfectDGBoundaryKanInfinityFunctor A r)
      (coherentNerveMap (dgKPositiveKanEnrichedFunctor A r)) :=
  functorIsoOfPointwiseInvertibleHomotopy (dgKSBoundaryPositiveHomotopy A r) (by
    intro p
    obtain ⟨P, rfl⟩ := (coherentNerveVertexEquiv (PerfDGInput.{u, v} A)).surjective p
    apply (isInvertibleEdge_congr (dgKSBoundaryPositiveHomotopy_component A r P)).mpr
    exact pointedKanObject_edge_isInvertible_of_piIsomorphism _
      (presentedPerfectDGBFStageComparison_piIsomorphism A r
        (presentedPerfectDGBFPositiveStage A r) P))

/-- 元の相対 Verdier 四角形に制限した、全 coherent 四角形どうしの同じ比較。 -/
def dgRelativeSBoundaryPositiveSquareIso (r : ℕ)
    (d : RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    FunctorIso (d.square ≫ presentedPerfectDGBoundaryKanInfinityFunctor A r)
      (d.square ≫ coherentNerveMap (dgKPositiveKanEnrichedFunctor A r)) :=
  (dgKSBoundaryPositiveIso A r).precomp d.square

end SerrePositivity.KST.Fibration
