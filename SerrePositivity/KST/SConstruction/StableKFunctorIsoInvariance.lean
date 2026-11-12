module
public import SerrePositivity.KST.SConstruction.StableBoundaryFunctorIsoComponents
public import SerrePositivity.KST.SConstruction.PointedKanReplacementComponents
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor
public import SerrePositivity.KST.SConstruction.SpectrumIntegerComponentEquality
public import SerrePositivity.KST.Spectra.PointedCurryingParameterComponents

/-! # 元の BF K の整数 π 作用の完全関手同型不変性
概要：関手同型を持つ完全関手は、既存の K の全整数 π に同じ作用を与える。
方針：零境界商の基点固定成分を Kan 置換と loop へ送り、単射置換射影で反映する。
規約：全段の成分等号を使う。使われ方：元の実 Perf 評価四角形の整数 π 自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 関手同型を持つ完全関手の、元の Kan 境界商射の基点固定成分は等しい。 -/
lemma stableBoundaryKanMap_component_of_functorIso (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    componentOf ((boundaryKanRealizationFunctor r).map (stableExactInputMap F)) =
      componentOf ((boundaryKanRealizationFunctor r).map (stableExactInputMap G)) :=
  pointedKanReplacement_map_component (stableBoundaryReducedMap_component_of_functorIso r e)

/-- 同じ関手同型から、零段を含む元の K の全段の基点固定成分等号を得る。 -/
lemma stableKRawMap_component_of_functorIso (n : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    componentOf (kKanSequenceLevelMap (stableExactInputMap F) n) =
      componentOf (kKanSequenceLevelMap (stableExactInputMap G) n) := by
  cases n with
  | zero =>
    exact componentOf_ihom_map PointedSimplicialSet.circle.{u}
      (stableBoundaryKanMap_component_of_functorIso 0 e)
  | succ r => exact stableBoundaryKanMap_component_of_functorIso r e

/-- 元の単射 BF 模型でも、完全関手同型は全段の基点固定成分を保つ。 -/
lemma stableKSpectrumMap_component_of_functorIso (n : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) :
    componentOf ((kSpectrumMap (stableExactInputMap F)).app n) =
      componentOf ((kSpectrumMap (stableExactInputMap G)).app n) := by
  apply pointedComponent_cancel_right_of_piIsomorphism
    ((monicKKanSequenceProjection (stableCategoryModel D)).app n)
    (monicKKanSequenceProjection_piIsomorphism (stableCategoryModel D) n)
  exact (monicKKanSequenceMap_projection_component (stableExactInputMap F) n).trans
    ((componentOf_comp_left (stableKRawMap_component_of_functorIso n e)
      ((monicKKanSequenceProjection (stableCategoryModel C)).app n)).trans
        (monicKKanSequenceMap_projection_component (stableExactInputMap G) n).symm)

/-- 同じ完全関手の関手同型は、元の実 BF K 射の全整数 π 作用を一致させる。 -/
lemma stableKHomotopyMap_eq_of_functorIso
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {F G : C ⟶ D} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F.hom G.hom) (j : ℤ) :
    kHomotopyMap (stableExactInputMap F) j = kHomotopyMap (stableExactInputMap G) j :=
  spectrumHomotopyMap_eq_of_levelwise_component _ _
    (fun n => stableKSpectrumMap_component_of_functorIso n e) j

/-- 元の安定模型の同じ完全射について、関手同型から整数 π 作用の等号を得る。 -/
lemma kHomotopyMap_eq_of_exact_functorIso {X Y : StableModel.{u}} (f g : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.val)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) (j : ℤ) : kHomotopyMap f j = kHomotopyMap g j := by
  let C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} := ⟨X.carrier, inferInstance, inferInstance⟩
  let D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} := ⟨Y.carrier, inferInstance, inferInstance⟩
  let F : C ⟶ D := ⟨f.val, hf⟩
  let G : C ⟶ D := ⟨g.val, hg⟩
  exact stableKHomotopyMap_eq_of_functorIso (F := F) (G := G) e j

end SerrePositivity.KST.SConstruction
