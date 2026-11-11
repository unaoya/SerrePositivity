module

public import SerrePositivity.KST.Spectra.SpectrumTail
public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：一段の添字移動を Sp の全単体上の関手にする。
方針：整合写像族の零段を落とし、評価によって単位と合成の保存を検査する。
規約：通常の対象関手だけでなく実際の豊穣関手を構成する。
使われ方：native loop 関手の逆と比較する候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 整合写像の零段を忘れる実際の写像空間の射。 -/
def tailMapping (X Y : OmegaSpectrum.{u}) : mappingSpace X Y ⟶ mappingSpace (tail X) (tail Y) :=
  TruncatedMapping.familyLift
    (fun n ↦ ((tail X).level n).space) (fun n ↦ ((tail Y).level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((tail X).level n).space) (tail X).sigma
    (mappingStep (tail X) (tail Y)) (fun n ↦ evaluation X Y (n + 1))
    (fun n ↦ evaluation_condition X Y (n + 1))

@[reassoc (attr := simp)]
lemma tailMapping_evaluation (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    tailMapping X Y ≫ evaluation (tail X) (tail Y) n = evaluation X Y (n + 1) :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n

local instance tailEnrichedSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 一段の添字移動は実際の BF 単体的圏の豊穣関手。 -/
def tailEnriched : EnrichedFunctor SSet.{u} OmegaSpectrum.{u} OmegaSpectrum.{u} where
  obj := tail
  map := tailMapping
  map_id X := by
    apply mapping_hom_ext
    intro n
    change (mappingIdentity X ≫ tailMapping X X) ≫ evaluation (tail X) (tail X) n =
      mappingIdentity (tail X) ≫ evaluation (tail X) (tail X) n
    rw [Category.assoc, tailMapping_evaluation, mappingIdentity_evaluation,
      mappingIdentity_evaluation]
    rfl
  map_comp X Y Z := by
    apply mapping_hom_ext
    intro n
    change (mappingComposition X Y Z ≫ tailMapping X Z) ≫
        evaluation (tail X) (tail Z) n =
      ((tailMapping X Y ⊗ₘ tailMapping Y Z) ≫
        mappingComposition (tail X) (tail Y) (tail Z)) ≫ evaluation (tail X) (tail Z) n
    rw [Category.assoc, tailMapping_evaluation, mappingComposition_evaluation,
      Category.assoc, mappingComposition_evaluation]
    dsimp only [compositionFamily]
    rw [← Category.assoc, tensorHom_comp_tensorHom,
      tailMapping_evaluation, tailMapping_evaluation]
    rfl

/-- 元の Sp の全単体上の一段移動関手。 -/
def nativeTail : Sp.{u} ⟶ Sp.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap tailEnriched

/-- 関手としての一段移動は元の BF 対象を一段ずらす。 -/
lemma nativeTail_vertex (X : OmegaSpectrum.{u}) :
    nativeTail.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (tail X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex tailEnriched X

end SerrePositivity.KST.Spectra.OmegaSpectrum
