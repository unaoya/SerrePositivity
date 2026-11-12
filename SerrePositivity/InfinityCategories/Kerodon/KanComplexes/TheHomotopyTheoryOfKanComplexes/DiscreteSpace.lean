module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEnrichedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomOrdinary
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.VertexDiscreteFunctionSimplices
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
概要：集合の離散空間を作り、零切り捨てられた空間をその本質像で表す。
方針：通常の nerve から Kan 複体の coherent nerve に移し、両側の写像空間を写像の集合と比較する。
使われ方：集合値前層の空間値前層への埋め込み。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial


/-- 集合と写像を定値単体的集合とその間の射に送る。 -/
def setsToKan : Type u ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj T := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_kan T⟩
  map f := (Functor.const SimplexCategoryᵒᵖ).map f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 離散 Kan 複体への同じ関手の旧名。 -/
abbrev discreteKanFunctor : Type u ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := setsToKan

namespace DiscreteSpaceModel

/-- 0・1 単体にはそれぞれ標準頂点・標準辺を直接返す。 -/
def simplex : ∀ n : ℕ, (nerve (Type u)) _⦋n⦌ → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n⦌
  | 0, s => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (setsToKan.obj (s.obj 0))
  | 1, s => (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (setsToKan.map s.hom)).edge
  | n + 2, s => (nerveMap setsToKan ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject).app
      (Opposite.op ⦋n + 2⦌) s

lemma simplex_eq (n : ℕ) (s : (nerve (Type u)) _⦋n⦌) :
    simplex n s = (nerveMap setsToKan ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject).app _ s := by
  match n with
  | 0 =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
      ((nerveMap setsToKan ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject).app (Opposite.op ⦋0⦌) s)
  | 1 =>
    obtain ⟨T, U, f, rfl⟩ := ComposableArrows.mk₁_surjective s
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (setsToKan.map f)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _).app (Opposite.op ⦋1⦌)
        ((nerveMap setsToKan).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f))
    rw [nerveMap_app_mk₁, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge]
  | n + 2 => rfl

end DiscreteSpaceModel

/-- 集合の圏から空間の ∞ 圏への離散埋め込み。 -/
def discreteSpaceInclusion : nerve (Type u) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app n := ↾DiscreteSpaceModel.simplex n.unop.len
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    change DiscreteSpaceModel.simplex m.unop.len ((nerve (Type u)).map f s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map f (DiscreteSpaceModel.simplex n.unop.len s)
    simp only [DiscreteSpaceModel.simplex_eq]
    exact ConcreteCategory.congr_hom
      ((nerveMap setsToKan ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject).naturality f) s

lemma discreteSpaceInclusion_vertex (T : Type u) :
    discreteSpaceInclusion.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (setsToKan.obj T) := rfl

lemma discreteSpaceInclusion_edge {T U : Type u} (f : T ⟶ U) :
    ((nerve.edgeMk f).map discreteSpaceInclusion).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (setsToKan.map f)).edge := rfl

/-- 集合値図式の離散化を評価すると、成分集合の離散頂点を得る。 -/
lemma discreteSpaceInclusion_diagramVertex {C : Type u} [SmallCategory C]
    (P : C ⥤ Type u) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (P ⋙ setsToKan)).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) =
      discreteSpaceInclusion.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (P.obj c)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 集合値自然変換を Kan 値図式として実現した辺を c で評価する式。 -/
lemma discreteSpaceInclusion_diagramEdge {C : Type u} [SmallCategory C]
    {P Q : C ⥤ Type u} (φ : P ⟶ Q) (c : C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge (F := ⟨P ⋙ setsToKan, trivial⟩)
      (G := ⟨Q ⋙ setsToKan, trivial⟩)
      (Functor.whiskerRight (Functor.whiskerRight φ setsToKan) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).edge =
        ((nerve.edgeMk (φ.app c)).map discreteSpaceInclusion).edge := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge_at]
  rfl

/-- 図式の辺が Kan 値自然変換の辺であるとき、その評価は集合写像の離散辺。 -/
lemma discreteSpaceInclusion_presheafInclusion_edge {C : Type u} [SmallCategory C]
    (I : nerve (C ⥤ Type u) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))).obj
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) {P Q : C ⥤ Type u} (φ : P ⟶ Q)
    (hI : ((nerve.edgeMk φ).map I).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge (F := ⟨P ⋙ setsToKan, trivial⟩)
        (G := ⟨Q ⋙ setsToKan, trivial⟩)
        (Functor.whiskerRight (Functor.whiskerRight φ setsToKan) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).edge)
    (c : C) :
    ((nerve.edgeMk φ).map (I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))).edge =
      ((nerve.edgeMk (φ.app c)).map discreteSpaceInclusion).edge :=
  by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C))
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))).app (Opposite.op ⦋1⦌)
      ((nerve.edgeMk φ).map I).edge = _
    rw [hI]
    exact discreteSpaceInclusion_diagramEdge φ c

/-- 離散空間と同値な空間。 -/
def Is0TruncatedSpace (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : Prop :=
  ∃ T : Type u, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (discreteSpaceInclusion.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T)))

/-- strict Segal 性により、始点に固定された n 単体は最後の辺で決まる。 -/
private lemma pinched_ext_last {X : SSet.{u}} [X.IsStrictSegal] {x y : X _⦋0⦌}
    {n : ℕ} {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n}
    (h : X.map (SimplexCategory.mkOfSucc (Fin.last n)).op s.val =
         X.map (SimplexCategory.mkOfSucc (Fin.last n)).op t.val) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  apply (SSet.IsStrictSegal.segal (X := X) (n + 1)).injective
  apply SSet.Path.ext'
  intro i
  induction i using Fin.lastCases with
  | last => exact h
  | cast i =>
    have he : SimplexCategory.mkOfSucc i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n =
        SimplexCategory.mkOfSucc i.castSucc := by
      ext j
      fin_cases j <;> rfl
    change X.map (SimplexCategory.mkOfSucc i.castSucc).op s.val =
      X.map (SimplexCategory.mkOfSucc i.castSucc).op t.val
    rw [← he, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, s.source, t.source]

private lemma pinched_last_injective {X : SSet.{u}} [X.IsStrictSegal] {x y : X _⦋0⦌}
    (n : ℕ) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) := by
  intro s t h
  apply pinched_ext_last
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)) =
      SimplexCategory.mkOfSucc (Fin.last n) := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro j
    induction j using Fin.lastCases with
    | last => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last _
    | cast j => fin_cases j; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _
  have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val h
  change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))).op s.val =
    X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))).op t.val at hh
  rwa [hi] at hh

private abbrev functionLabels (T U : Type u) : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (T ⟶ U))

private def labelledVertices {T U : Type u} {X : SSet.{u + 1}} (f : (T ⟶ U) → X _⦋0⦌) :
    functionLabels T U ⟶ X where
  app n := ↾fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f a.down) n.unop.len
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback _ α.unop).symm

private lemma labelledVertices_isIso {T U : Type u} {X : SSet.{u + 1}}
    (f : (T ⟶ U) → X _⦋0⦌) (hf : Function.Bijective f)
    (hX : ∀ n, Function.Injective (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op)) :
    IsIso (labelledVertices f) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  apply (isIso_iff_bijective _).2
  let v := X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op
  have hv (a : ULift.{u + 1} (T ⟶ U)) :
      v ((labelledVertices f).app (Opposite.op ⦋n⦌) a) = f a.down :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback _ _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  constructor
  · intro a b h
    apply ULift.ext
    apply hf.1
    simpa only [hv] using congrArg v h
  · intro s
    obtain ⟨a, ha⟩ := hf.2 (v s)
    exact ⟨ULift.up a, hX n ((hv (ULift.up a)).trans ha)⟩

private def sourceLabel {T U : Type u} (f : T ⟶ U) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm (nerve.edgeMk (C := Type u) f).toTruncated

private lemma sourceLabel_bijective (T U : Type u) :
    Function.Bijective (sourceLabel (T := T) (U := U)) := by
  constructor
  · intro f g h
    have he : nerve.edgeMk f = nerve.edgeMk g := by
      apply SSet.Edge.ext
      exact congrArg (fun v => ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _) v).edge) h
    simpa only [nerve.homEquiv_edgeMk] using congrArg nerve.homEquiv he
  · intro s
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _) s
    let e' : (nerve (Type u)).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U) :=
      ⟨e.edge, e.src_eq, e.tgt_eq⟩
    obtain ⟨f, hf⟩ := nerve.edgeMk_surjective e'
    refine ⟨f, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).injective ?_⟩
    rw [sourceLabel, Equiv.apply_symm_apply, hf]
    rfl

private abbrev enrichedHom (T U : Type u) :=
  (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (setsToKan.obj T) (setsToKan.obj U))

private def enrichedLabel {T U : Type u} (f : T ⟶ U) : (enrichedHom T U) _⦋0⦌ :=
  ULift.up (SimplicialCategory.homEquiv' _ _ (setsToKan.map f))

private lemma enrichedLabel_bijective (T U : Type u) :
    Function.Bijective (enrichedLabel (T := T) (U := U)) := by
  have hf : Function.Bijective (setsToKan.map (X := T) (Y := U)) := by
    constructor
    · intro f g h
      exact congrArg (fun m : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete U => (m.app (Opposite.op ⦋0⦌))) h
    · intro f
      refine ⟨f.app (Opposite.op ⦋0⦌), ?_⟩
      apply NatTrans.ext
      funext n
      exact (f.naturality (SimplexCategory.const n.unop ⦋0⦌ 0).op).symm
  exact Equiv.ulift.symm.bijective.comp ((SimplicialCategory.homEquiv' _ _).bijective.comp hf)

private lemma enriched_last_injective (T U : Type u) (n : ℕ) :
    Function.Injective ((enrichedHom T U).map
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) := by
  intro s t h
  apply ULift.ext
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete U
  let v := (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op
  change (ULift.up (((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete D)).obj Y).map v s.down) : ULift.{u + 1} _) =
    ULift.up (((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete D)).obj Y).map v t.down) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct (A := D) (X := Y) s.down,
    ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct (A := D) (X := Y) t.down]
  congr 1
  funext a
  let ev := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := D) (X := Y) a
  have e := congrArg (fun w => ev.app (Opposite.op ⦋0⦌) w.down) h
  exact ((ConcreteCategory.congr_hom (ev.naturality v) s.down).symm.trans
    (e.trans (ConcreteCategory.congr_hom (ev.naturality v) t.down)))

/-- 両側の写像空間に同じ写像の集合を入れ、頂点での比較を全次数に移す。 -/
private lemma discretePinchedMap_equivalence (T U : Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap discreteSpaceInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) := by
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap discreteSpaceInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)
  let a := labelledVertices (sourceLabel (T := T) (U := U))
  let b := labelledVertices (enrichedLabel (T := T) (U := U))
  let e := eqToIso (congrArg₂ (fun x y => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (discreteSpaceInclusion_vertex T) (discreteSpaceInclusion_vertex U))
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (setsToKan.obj T) (setsToKan.obj U)
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete (T ⟶ U)) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_kan _
  have : IsIso a :=
    labelledVertices_isIso _ (sourceLabel_bijective T U) (fun n => pinched_last_injective n)
  have : IsIso b :=
    labelledVertices_isIso _ (enrichedLabel_bijective T U) (enriched_last_injective T U)
  have he (f : T ⟶ U) : (M ≫ e.hom).app _ (sourceLabel f) = H.app _ (enrichedLabel f) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rw [show ((M ≫ e.hom).app _ (sourceLabel f)).val = (M.app _ (sourceLabel f)).val from
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_eqToHom_app_val (discreteSpaceInclusion_vertex T)
        (discreteSpaceInclusion_vertex U) (M.app _ (sourceLabel f))]
    exact (discreteSpaceInclusion_edge f).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary _).symm
  have comm : a ≫ M ≫ e.hom = b ≫ H := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro f
    change (M ≫ e.hom).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (sourceLabel f.down) n) =
      H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (enrichedLabel f.down) n)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, he]
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso b)).isQCatEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence (setsToKan.obj T) (setsToKan.obj U))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (b ≫ H) at h
  rw [← comm] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.cancel_right
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso a)).isQCatEquivalence.cancel_left h)

lemma discreteSpaceInclusion_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful discreteSpaceInclusion.{u} := by
  intro x y
  obtain ⟨T, rfl⟩ := (nerveEquiv (C := Type u)).symm.surjective x
  obtain ⟨U, rfl⟩ := (nerveEquiv (C := Type u)).symm.surjective y
  exact (discretePinchedMap_equivalence T U).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
