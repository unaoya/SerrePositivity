module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityJointMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoherentMapRealization
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedElementsReconstruction

/-!
概要：元の weighted 密度の全評価を、共同 Hom から共同分類への一つの coherent 変換へ移す。
方針：同じ復元射に沿って相対射を延長し、c1 の元の写像空間比較で実現する。
規約：元の全評価との相対同型も保持。使われ方：全添字上の表現可能図式の密度比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)
abbrev weightedDensityProjection : weightedNerve (rightFibrationTotalDiagram F) ⟶ C :=
  weightedNerveParameter (B := C) (rightFibrationProjectionCocone F).ι
local notation "ρ" => weightedDensityProjection F
local notation "H" => twistedElementsHomDiagram (C := C) ρ
local notation "G" => weightedDensityJointTargetDiagram F
local notation "r" => twistedElementsReconstruction (C := C) ρ

/-- 同じ全評価の相対射・比較同型・coherent な実現を一緒に保持する。 -/
structure WeightedDensityTransformation where
  map : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G
  over_base : map ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H
  evaluationIso : VertexIso
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (r ≫ smallLeftUnstraighteningProjection H) (r ≫ map) (by rw [Category.assoc, over_base]))
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (r ≫ smallLeftUnstraighteningProjection H) (weightedDensityTwistedJointMap F) (by
        rw [weightedDensityTwistedJointMap_projection, twistedElementsReconstruction_projection]))
  realization : CoherentMapRealization H G map over_base

local instance : Quasicategory (weightedNerve (rightFibrationTotalDiagram F)) := by
  have (i : I) : Quasicategory ((rightFibrationTotalDiagram F).obj i) :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  infer_instance

local instance : Quasicategory (C.op ⊗ weightedNerve (rightFibrationTotalDiagram F)) :=
  quasicategory_of_innerFibration (fst C.op (weightedNerve (rightFibrationTotalDiagram F)))

/-- 同じ全高次の weighted 密度評価を保つ実現データは、追加の同値性仮定なしに存在する。 -/
lemma weightedDensityTransformation_nonempty : Nonempty (WeightedDensityTransformation F) := by
  obtain ⟨L, hL, ⟨he⟩⟩ := exists_relativeFunctorExtension_of_precompositionEquivalence
    (smallLeftUnstraighteningProjection G) (smallLeftUnstraighteningProjection H) r
    (twistedElementsReconstruction_isPrecompositionEquivalence (C := C) ρ)
    (weightedDensityTwistedJointMap F) (by
      rw [weightedDensityTwistedJointMap_projection, twistedElementsReconstruction_projection])
  obtain ⟨R⟩ := coherentMapRealization_nonempty H G L hL
  exact ⟨⟨L, hL, he, R⟩⟩

/-- 元の全評価とその比較を持つ、一つの共同密度変換の実現を固定する。 -/
def weightedDensityTransformation : WeightedDensityTransformation F :=
  Classical.choice (weightedDensityTransformation_nonempty F)

/-- 元の weighted 全空間をパラメータにした、共同 Hom から元の共同分類への一つの変換。 -/
def weightedDensityJointHomotopy : SSet.Homotopy H G :=
  smallTransformationHomotopy H G (weightedDensityTransformation F).realization.transformation

end SerrePositivity.InfinityCategories.F2.Ind
