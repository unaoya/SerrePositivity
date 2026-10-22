module

public import SerrePositivity.InfinityCategories.F2.Ind.CoherentMapRealization
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafTwistedElementsMap
public import SerrePositivity.InfinityCategories.F2.Ind.TwistedElementsReconstruction
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEssentialExtension

/-!
概要：密度の大域評価を、元の共同 Hom 図式から元の F への一つの自然変換へ移す。
方針：同じ復元射に沿って相対射を延長し、c1 の写像空間比較で変換を実現する。
規約：延長の元の評価との同型も相対写像空間内に保持する。
使われ方：元の小さい Yoneda 図式の密度余錐への curry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "E" => smallRightUnstraightening F
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "r" => twistedElementsReconstruction p
local notation "q" => twistedElementsProjection p

/-- 同じ大域評価から得る相対射・その評価同型・c1 の変換を一緒に保持する。 -/
structure PresheafDensityTransformation where
  map : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G
  over : map ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H
  evaluationIso : VertexIso
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (r ≫ smallLeftUnstraighteningProjection H) (r ≫ map) (by rw [Category.assoc, over]))
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (r ≫ smallLeftUnstraighteningProjection H) (presheafTwistedElementsMap F) (by
        rw [presheafTwistedElementsMap_projection, twistedElementsReconstruction_projection]))
  realization : CoherentMapRealization H G map over

local instance : Quasicategory E := quasicategory_of_innerFibration p
local instance : Quasicategory (C.op ⊗ E) := quasicategory_of_innerFibration (fst C.op E)

/-- 元の全高次の評価を保つ同じ自然変換の実現データが存在する。 -/
lemma presheafDensityTransformation_nonempty : Nonempty (PresheafDensityTransformation F) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_relativeFunctorExtension_of_precompositionEquivalence
    (smallLeftUnstraighteningProjection G) (smallLeftUnstraighteningProjection H) r
    (twistedElementsReconstruction_isPrecompositionEquivalence p)
    (presheafTwistedElementsMap F) (by
      rw [presheafTwistedElementsMap_projection, twistedElementsReconstruction_projection])
  obtain ⟨R⟩ := coherentMapRealization_nonempty H G L hL
  exact ⟨⟨L, hL, e, R⟩⟩

/-- 密度の同じ自然変換と評価との比較を、一つ固定する。 -/
def presheafDensityTransformation : PresheafDensityTransformation F :=
  Classical.choice (presheafDensityTransformation_nonempty F)

/-- 全小さい元の圏をパラメータにした、同じ共同 Hom から元の F への自然変換。 -/
def presheafDensityJointHomotopy : SSet.Homotopy H G :=
  smallTransformationHomotopy H G (presheafDensityTransformation F).realization.transformation

end SerrePositivity.InfinityCategories.F2.Ind
