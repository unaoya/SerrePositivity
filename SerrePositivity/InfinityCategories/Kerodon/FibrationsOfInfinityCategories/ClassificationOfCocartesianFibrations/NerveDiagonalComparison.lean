module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictTransportKanDiagramInclusion

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalKanDiagramReindex

/-!
概要：底と図式の coherent パラメーターを同時に動かす標準単位。
方針：strict transport の像を全図式へ含め、混合評価で単位の自然性を検証する。
規約：底の射と高次の Hom をともに保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共同実現による大域的な単位。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：weighted nerve 後の strict transport を全 strict Kan 図式の自己作用にする。
方針：構成済みの二つの豊穣関手と像の包含を合成する。
規約：全変換空間への作用を保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、単位の両端を同じ図式の圏に置く。 -/
def weightedNerveTransportDiagramEnriched (C : Type u) [Category.{u} C] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveKanEnriched C).comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStrictTransportEnriched).comp SSet
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictTransportKanDiagramEnriched

/-- 概要：単位は底の射と高次の変換を同時に評価しても自然。
方針：豊穣自然性を成分で評価した後、終域図式の単位の通常の自然性を使う。
規約：変換のパラメーターと評価の次数は独立。
使われ方：Kerodon §5.6.5（Tag 028U）、対角比較の全次数の可換性。 -/
lemma weightedNerveTransportUnit_mixedNaturality
    {C : Type u} [Category.{u} C] (F G : C ⥤ SSet.{u})
    {c d : C} (f : c ⟶ d) {n k : SimplexCategoryᵒᵖ}
    (θ : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G).obj n) (α : n ⟶ k) (x : (F.obj c).obj k) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G)).map f).app k
      (((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingSpaceMap F G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G)).app n θ).val c).app k α)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).app c).app k x)) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit G).app d).app k
      ((G.map f).app k ((θ.val c).app k α x)) := by
  have h := congrArg (fun m ↦ (((m.app n θ).val c).app k α x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit_enrichedNaturality F G)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit G).app c).app k ((θ.val c).app k α x) =
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingSpaceMap F G ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportMappingSpaceMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection G)).app n θ).val c).app k (α ≫ 𝟙 k))
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit F).app c).app k x) at h
  simp only [Category.comp_id] at h
  rw [← h]
  exact (congrArg (fun t ↦ t.app k ((θ.val c).app k α x))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit G).naturality f)).symm

/-- 概要：底と coherent 図式の対角評価の間の単位は豊穣な比較。
方針：各頂点で標準単位を取り、順向きの Hom で混合自然性を使う。
規約：任意の線形順序の添字を許す。
使われ方：Kerodon §5.6.5（Tag 028U）、二点図式の共同実現を作る入力。 -/
noncomputable def weightedNerveDiagonalKanComparison
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation A F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation A (F.comp SSet (weightedNerveTransportDiagramEnriched C))) := by
  refine ⟨(fun i ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit
    ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app (A.obj i.as)), ?_⟩
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, P⟩
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom A
      (F.comp SSet (weightedNerveTransportDiagramEnriched C)) i j).app n P).app n (𝟙 n)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app (A.obj i.as)).app n x) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportUnit ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app (A.obj j.as)).app n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom A F i j).app n P).app n (𝟙 n) x)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le A F i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le A (F.comp SSet (weightedNerveTransportDiagramEnriched C)) i j hij]
  exact weightedNerveTransportUnit_mixedNaturality
    ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (A.map (homOfLE hij)) ((F.map i j).app n P) (𝟙 n) x

/-- 概要：対角評価の単位を二点の Kan 値図式の coherent な族にする。
方針：混合自然性から得た豊穣比較を二点図式として実現する。
規約：底と図式の二つの変数を同じ添字で評価する。
使われ方：Kerodon §5.6.5（Tag 028U）、標準単位の共同実現の単体。 -/
noncomputable def weightedNerveDiagonalArrow
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject (ULift.{u} (Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched (weightedNerveDiagonalKanComparison A F)

/-- 概要：単位の二点図式は底とパラメーターの同時添字変換と可換。
方針：両端で対角評価の添字変換則を使う。
規約：任意の単調写像を許し、面と退化をともに含む。
使われ方：Kerodon §5.6.5（Tag 028U）、共同実現の単体的自然性。 -/
lemma weightedNerveDiagonalArrow_reindex
    {C J K : Type u} [Category.{u} C] [LinearOrder J] [LinearOrder K]
    (α : J →o K) (A : K ⥤ C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening K) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)) :
    (SimplicialThickening.functor α).comp SSet (weightedNerveDiagonalArrow A F) =
      weightedNerveDiagonalArrow (α.toFunctor ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  rcases t with ⟨t⟩
  fin_cases t
  · have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom A F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (α.toFunctor ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le A F _ _ (α.monotone hij),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · let G := F.comp SSet (weightedNerveTransportDiagramEnriched C)
    have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom A G ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (α.toFunctor ⋙ A)
        ((SimplicialThickening.functor α).comp SSet G) i j).app n P
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le A G _ _ (α.monotone hij),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl

/-- 概要：底を固定した対角比較は、既存の一対象評価の豊穣比較になる。
方針：底の恒等射で混合 Hom を対象成分へ簡約する。
規約：比較の二点図式そのものの等式。
使われ方：Kerodon §5.6.5（Tag 028U）、共同比較の点ごとの可逆性の検査。 -/
lemma weightedNerveDiagonalArrow_constant
    {C J : Type u} [Category.{u} C] [LinearOrder J] (c : C)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening J) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject C)) :
    weightedNerveDiagonalArrow ((Functor.const J).obj c) F =
      F.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTransportKanComparison c)) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  rcases t with ⟨t⟩
  fin_cases t
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom ((Functor.const J).obj c) F i j).app n P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ F i j
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((F.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (𝟙 c)
      ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app n) P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramMixedHom_base_id]
    rfl
  · let G := F.comp SSet (weightedNerveTransportDiagramEnriched C)
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom ((Functor.const J).obj c) G i j).app n P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ G i j
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((G.map i j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (𝟙 c)
      ((G.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((G.obj j).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app n) P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramMixedHom_base_id]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
