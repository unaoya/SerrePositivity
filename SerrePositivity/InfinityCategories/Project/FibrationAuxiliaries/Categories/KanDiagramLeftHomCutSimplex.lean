module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalCutHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramRealization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedLeftHomIntervalEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism

/-!
概要：左 Hom 区間と元の底の射列の共同評価を、同じ切断座標で記述する。
方針：実際の coherent な左区間の単体を対角評価し、対象と混合 Hom を正規化する。
規約：同じ strict 変換の全パラメーターと、元の底の射を保持する。
使われ方：weighted pointed prism の正頂点側を、元の共同実現の底として組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories


private def cutTargetDiagram {I : Type u} [SmallCategory I] (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    ULift.{u} (Fin 1) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I := (Functor.const _).obj G

/-- 元の左 Hom 区間の単体を、同じ底の射列上で共同評価する。 -/
def kanDiagramLeftHomCutSimplex {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramDiagonalSimplex σ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval F G).app (Opposite.op ⦋n⦌)
    (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom F G)).hom.app _ (ULift.up s)))

/-- 時刻零の共同評価の対象は、元の始域図式の同じ底対象での値。 -/
lemma kanDiagramLeftHomCutSimplex_obj_zero {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0) :
    (kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up a⟩ = F.val.obj (σ.obj a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero (cutTargetDiagram G) F (ULift.up 0) s t a ha
  exact congrArg (fun H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I => H.val.obj (σ.obj a)) h

/-- 時刻一の共同評価の対象は、元の終域図式の同じ底対象での値。 -/
lemma kanDiagramLeftHomCutSimplex_obj_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 1) :
    (kanDiagramLeftHomCutSimplex F G σ s t).obj ⟨ULift.up a⟩ = G.val.obj (σ.obj a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one (cutTargetDiagram G) F (ULift.up 0) s t a ha
  exact congrArg (fun H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I => H.val.obj (σ.obj a)) h

private lemma normalizedDiagonalKanHom {I J : Type u} [SmallCategory I] [LinearOrder J]
    (A : J ⥤ I)
    (R : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I))
    (a b : SimplicialThickening J) (hab : a.as ≤ b.as) {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I}
    (ha : R.obj a = F) (hb : R.obj b = G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom A R a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg (fun H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I => H.val.obj (A.obj a.as)) ha)
      (congrArg (fun H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I => H.val.obj (A.obj b.as)) hb)) =
    (R.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (A.map (homOfLE hab))
        (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  subst F
  subst G
  simp only [eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le A R a b hab

/-- 正頂点間の実際の混合 Hom は、同じ切断係数と底の射による strict 混合評価。 -/
lemma kanDiagramLeftHomCutSimplex_mixedHom {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a b : Fin (n + 1)) (hab : a ≤ b)
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    (kanDiagramLeftHomCutSimplex F G σ s t).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t a ha)
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t b hb)) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShiftFunctor a b) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap (stdSimplex.objEquiv t).toOrderHom hb ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (σ.map (homOfLE hab))
            (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval F G).app (Opposite.op ⦋n⦌)
    (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom F G)).hom.app _ (ULift.up s))
  have h0 : R.obj ⟨ULift.up a⟩ = F :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero (cutTargetDiagram G) F (ULift.up 0) s t a ha
  have h1 : R.obj ⟨ULift.up b⟩ = G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one (cutTargetDiagram G) F (ULift.up 0) s t b hb
  have hd := normalizedDiagonalKanHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ) R
    ⟨ULift.up a⟩ ⟨ULift.up b⟩ hab h0 h1
  calc
    _ = (R.map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom h0 h1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (σ.map (homOfLE hab))
          (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := hd
    _ = _ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomIntervalMixedHom (cutTargetDiagram G) F (ULift.up 0) s t a b ha hb ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (σ.map (homOfLE hab))
          (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomIntervalMixedHom_eq_cut]
      simp only [Category.assoc]
      rfl

private lemma leftCut_strictMixedIdentity {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom f F F = curry' (F.map f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component,
    MonoidalClosed.id_eq, ← curry_natural_right]
  rfl

/-- 時刻零同士の共同評価の Hom は、元の始域図式の底の射そのものの定値評価。 -/
lemma kanDiagramLeftHomCutSimplex_hom_zero {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a b : Fin (n + 1)) (hab : a ≤ b)
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 0) :
    (kanDiagramLeftHomCutSimplex F G σ s t).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t a ha)
        (kanDiagramLeftHomCutSimplex_obj_zero F G σ s t b hb)) =
      SemiCartesianMonoidalCategory.toUnit _ ≫
        curry' (show (F.val.obj (σ.obj a)).obj ⟶ (F.val.obj (σ.obj b)).obj from
          F.val.map (σ.map (homOfLE hab))) := by
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval F G).app (Opposite.op ⦋n⦌)
    (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom F G)).hom.app _ (ULift.up s))
  have h0 : R.obj ⟨ULift.up a⟩ = F :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero (cutTargetDiagram G) F (ULift.up 0) s t a ha
  have h1 : R.obj ⟨ULift.up b⟩ = F :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero (cutTargetDiagram G) F (ULift.up 0) s t b hb
  have hu : R.map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom h0 h1) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet F :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomIntervalHom_zero (cutTargetDiagram G) F (ULift.up 0) s t a b ha hb
  have hd := normalizedDiagonalKanHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ) R
    ⟨ULift.up a⟩ ⟨ULift.up b⟩ hab h0 h1
  calc
    _ = (R.map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom h0 h1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (σ.map (homOfLE hab))
          (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := hd
    _ = _ := by
      rw [hu]
      change (SemiCartesianMonoidalCategory.toUnit _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫ _ = _
      rw [Category.assoc, leftCut_strictMixedIdentity]
      rfl

/-- 時刻一同士の共同評価の Hom は、元の終域図式の底の射そのものの定値評価。 -/
lemma kanDiagramLeftHomCutSimplex_hom_one {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) (a b : Fin (n + 1)) (hab : a ≤ b)
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 1)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    (kanDiagramLeftHomCutSimplex F G σ s t).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t a ha)
        (kanDiagramLeftHomCutSimplex_obj_one F G σ s t b hb)) =
      SemiCartesianMonoidalCategory.toUnit _ ≫
        curry' (show (G.val.obj (σ.obj a)).obj ⟶ (G.val.obj (σ.obj b)).obj from
          G.val.map (σ.map (homOfLE hab))) := by
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval F G).app (Opposite.op ⦋n⦌)
    (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom F G)).hom.app _ (ULift.up s))
  have h0 : R.obj ⟨ULift.up a⟩ = G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one (cutTargetDiagram G) F (ULift.up 0) s t a ha
  have h1 : R.obj ⟨ULift.up b⟩ = G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one (cutTargetDiagram G) F (ULift.up 0) s t b hb
  have hu : R.map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom h0 h1) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet G :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomIntervalHom_one (cutTargetDiagram G) F (ULift.up 0) s t a b ha hb
  have hd := normalizedDiagonalKanHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ) R
    ⟨ULift.up a⟩ ⟨ULift.up b⟩ hab h0 h1
  calc
    _ = (R.map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom h0 h1)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (σ.map (homOfLE hab))
          (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := hd
    _ = _ := by
      rw [hu]
      change (SemiCartesianMonoidalCategory.toUnit _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ≫ _ = _
      rw [Category.assoc, leftCut_strictMixedIdentity]
      rfl

/-- この同じ対角単体は、元の共同実現の左 Hom 区間 prism の実際の全評価。 -/
lemma kanDiagramLeftHomCutSimplex_prism {I : Type u} [SmallCategory I]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched I) F G rfl rfl))).app
      (Opposite.op ⦋n⦌) ((t, ULift.up σ), ULift.up s) =
    kanDiagramLeftHomCutSimplex F G σ s t := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramLeftHomInterval_uncurry]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram.realization, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramUniversalEnriched_toEnrichedFunctor,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism]
  simp only [uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
