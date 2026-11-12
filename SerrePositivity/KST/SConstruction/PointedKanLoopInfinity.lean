module
public import SerrePositivity.KST.SConstruction.PointedLoopEnrichment
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StrictConeFunctorImage

/-! # 点つき Kan 複体の coherent nerve 上の loop
概要：元の loop 模型の豊穣関手から、coherent nerve 上の実際の loop 関手を構成する。
方針：豊穣作用を Kan 対象の全部分圏へ制限し、通常の作用と strict な図式を照合する。
規約：基点と通常の loop 射を保ち、全入力単体で図式の等式を証明する。
使われ方：K の全入力 Ω 比較を、loop ∞ 関手を用いる構造へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の loop 対象を Kan 性とともに束ねる。 -/
def pointedKanLoopObject (X : PointedKanObject.{u}) : PointedKanObject.{u} :=
  ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj, loopSpace_kanComplex X.obj⟩

/-- 元の基点固定写像空間の作用を持つ、Kan 対象間の loop 豊穣関手。 -/
def pointedKanLoopEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedKanObject.{u} PointedKanObject.{u} where
  obj := pointedKanLoopObject
  map X Y := (pointedLoopHom X.obj Y.obj).right
  map_id X := pointedLoopHom_simplicial_id X.obj
  map_comp X Y Z := pointedLoopHom_simplicial_comp X.obj Y.obj Z.obj

/-- 豊穣 loop 関手の通常の作用。 -/
def pointedKanLoopFunctor : PointedKanObject.{u} ⥤ PointedKanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor pointedKanLoopEnrichedFunctor

/-- 通常の作用は、元の点つき射に元の loop を適用した射そのもの。 -/
lemma pointedKanLoopFunctor_map_hom {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    ((pointedKanLoopFunctor.map f).hom : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) =
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map f.hom := by
  apply (pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)).injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex pointedKanLoopEnrichedFunctor f
  change pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X.obj) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)
      ((pointedKanLoopFunctor.map f).hom) =
    (pointedLoopHom X.obj Y.obj).right.app _ (pointedHomVertexEquiv X.obj Y.obj f.hom) at h
  exact h.trans (pointedLoopHom_vertex f.hom)

/-- 点つき Kan 複体の coherent nerve 上の、実際の loop ∞ 関手。 -/
def pointedKanLoopInfinity : PointedKanInfinity.{u} ⟶ PointedKanInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanLoopEnrichedFunctor

/-- Loop ∞ 関手は対象の頂点で元の loop 模型を返す。 -/
lemma pointedKanLoopInfinity_vertex (X : PointedKanObject.{u}) :
    pointedKanLoopInfinity.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (pointedKanLoopObject X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex pointedKanLoopEnrichedFunctor X

/-- Kan 値の strict な図式に対し、loop の通常の作用を元の点つき図式として回収する。 -/
lemma pointedKanLoopDiagram_eq {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :
    pointedKanDiagram F hF ⋙ pointedKanLoopFunctor =
      pointedKanDiagram
        (F ⋙ PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
        (fun i => @loopSpace_kanComplex (F.obj i) (hF i)) := by
  refine CategoryTheory.Functor.ext (fun _ => ?_) ?_
  · rfl
  intro i j f
  simp only [CategoryTheory.Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext _
  exact pointedKanLoopFunctor_map_hom ((pointedKanDiagram F hF).map f)

/-- 全入力単体で、loop の strict な図式は実際の loop ∞ 関手による後合成に一致する。 -/
lemma pointedKanLoopInfinity_diagram {I : Type u} [SmallCategory I]
    (F : I ⥤ PointedSimplicialSet.{u}) (hF : ∀ i, KanComplex (F.obj i).right) :
    pointedKanCoherentDiagram F hF ≫ pointedKanLoopInfinity =
      pointedKanCoherentDiagram
        (F ⋙ PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u})
        (fun i => @loopSpace_kanComplex (F.obj i) (hF i)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointedKanDiagram F hF) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap pointedKanLoopEnrichedFunctor = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentDiagram_postcomp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (pointedKanDiagram F hF ⋙ pointedKanLoopFunctor) = _
  rw [pointedKanLoopDiagram_eq]
  rfl

end SerrePositivity.KST.SConstruction
