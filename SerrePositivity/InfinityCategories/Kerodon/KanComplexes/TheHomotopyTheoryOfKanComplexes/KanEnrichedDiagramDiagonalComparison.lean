module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison

/-!
概要：Kan 値豊穣図式の比較を、添字と全対象の同時対角評価で保つ。
方針：成分の豊穣自然性と添字の自然性を同時対角評価へ適用する。
規約：高次の Hom と単体の添字を同時に動かす。
使われ方：切断図式全体の比較を coherent な一つの族へ実現する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：共同対角評価の間の図式の比較は Kan 値豊穣比較。
方針：各対角の頂点で図式の比較を取り、混合自然性を高次の Hom に適用する。
規約：coherent な対象図式も線形添字の底図式も任意。
使われ方：比較の二点図式を全次数で実現する入力。 -/
def KanEnrichedDiagramComparison.diagonalKanComparison
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I : Type u} [Category.{u} J] [LinearOrder I]
    {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (σ : I ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ
        (T.comp SSet D.toEnrichedFunctor))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ
        (T.comp SSet E.toEnrichedFunctor)) := by
  refine ⟨(fun i ↦ (η.app (T.obj i)).app (σ.obj i.as)), ?_⟩
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, P⟩
  have hij := SimplicialThickening.Path.le (P.obj 0)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ
      (T.comp SSet E.toEnrichedFunctor) i j).app n P).app n
        (𝟙 n) (((η.app (T.obj i)).app (σ.obj i.as)).app n x) =
    ((η.app (T.obj j)).app (σ.obj j.as)).app n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ
        (T.comp SSet D.toEnrichedFunctor) i j).app n P).app n
          (𝟙 n) x)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
  exact η.mixedNaturality (T.obj i) (T.obj j)
    (σ.map (homOfLE hij)) ((T.map i j).app n P) (𝟙 n) x

/-- 概要：共同対角評価の比較を二点の Kan 図式に束ねる。
方針：各成分の豊穣自然な比較から既存の二点図式を作る。
規約：同じ比較の成分をそのまま使う。
使われ方：全パラメーターの比較の共同実現。 -/
def KanEnrichedDiagramComparison.diagonalArrow
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I : Type u} [Category.{u} J] [LinearOrder I]
    {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (σ : I ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    EnrichedFunctor SSet.{u} (SimplicialThickening I)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject (ULift.{u} (Fin 2))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched (KanEnrichedDiagramComparison.diagonalKanComparison η σ T)

/-- 概要：比較の二点図式は添字の同時制限と厳密に可換。
方針：二つの成分で対角 Hom の添字変換則を計算する。
規約：全ての単調写像、面、退化を含む。
使われ方：共同実現の単体的自然性。 -/
lemma KanEnrichedDiagramComparison.diagonalArrow_reindex
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I K : Type u} [Category.{u} J] [LinearOrder I] [LinearOrder K]
    {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (α : I →o K) (σ : K ⥤ J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening K) C) :
    (SimplicialThickening.functor α).comp SSet (KanEnrichedDiagramComparison.diagonalArrow η σ T) =
      KanEnrichedDiagramComparison.diagonalArrow η (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet T) := by
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
  · let F := T.comp SSet D.toEnrichedFunctor
    have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl
  · let F := T.comp SSet E.toEnrichedFunctor
    have hij := SimplicialThickening.Path.le (P.obj 0)
    change (((SimplicialThickening.functor α).map i j ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (α.toFunctor ⋙ σ)
        ((SimplicialThickening.functor α).comp SSet F) i j).app n P
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le σ F _ _ (α.monotone hij),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
    rfl

/-- 概要：底を固定した共同対角比較は既存の一対象の比較へ戻る。
方針：底の恒等射で混合 Hom を成分評価へ簡約する。
規約：比較の二点図式そのものの厳密な等式。
使われ方：全パラメーターの比較の点ごとの可逆性を検証する。 -/
lemma KanEnrichedDiagramComparison.diagonalArrow_constant
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J I : Type u} [Category.{u} J] [LinearOrder I]
    {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (j : J)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    KanEnrichedDiagramComparison.diagonalArrow η ((Functor.const I).obj j) T =
      T.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonArrowEnriched
        (η.component j)) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i k
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  apply Subtype.ext
  funext t
  rcases t with ⟨t⟩
  fin_cases t
  · let F := T.comp SSet D.toEnrichedFunctor
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom ((Functor.const I).obj j) F i k).app n P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ F i k
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((F.map i k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (𝟙 j)
      ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj k).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app n) P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramMixedHom_base_id]
    rfl
  · let F := T.comp SSet E.toEnrichedFunctor
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom ((Functor.const I).obj j) F i k).app n P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ F i k
      (SimplicialThickening.Path.le (P.obj 0))]
    change ((F.map i k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMixedHom (𝟙 j)
      ((F.obj i).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ((F.obj k).val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).app n) P = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramMixedHom_base_id]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
