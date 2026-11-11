module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SourceCoherentMixedHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.RightIntervalCutHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportHomCutSimplex

/-!
概要：実際の分類作用の切断した共同評価で、固定成分に向かう混合 Hom を計算する。
方針：切断の path 作用と元の混合作用を合成し、成分 fiber の定値性を使う。
規約：元の全パラメーターの prism と同じ対角評価を保持する。
使われ方：第一三角形と指定された strict 合成三角形の高次 Hom の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ source 成分 fiber の切断した coherent な混合 Hom は、指定頂点に定値。 -/
lemma cocartesianHomSourceComponent_cutMixedHom
    {C : Type u} [Category.{u} C] {c d : C} (f : c ⟶ d)
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d))) _⦋0⦌) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent F G d) b) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex s.val.down t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero s.val.down t i hi)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one s.val.down t j hj))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramMixedHom f F G =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (F.val.map f)).app (G.val.obj d))).app
        (Opposite.op ⦋0⦌) b.down) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_mixedHom s.val.down t i j hi hj]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent_mixedHom_yoneda f F G b s]
  simp only [SSet.comp_const]

/-- 対角評価の対象を元の図式へ正規化すると、同じ Hom の混合評価になる。 -/
lemma diagonalCocartesianTransportDiagramHom_normalized
    {C J : Type u} [Category.{u} C] [LinearOrder J] (A : J ⥤ C)
    (R : EnrichedFunctor SSet.{u} (SimplicialThickening J)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C))
    (i j : SimplicialThickening J) (hij : i.as ≤ j.as)
    {F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C} (hi : R.obj i = F) (hj : R.obj j = G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianTransportDiagramHom A R i j ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (congrArg (fun H ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue H (A.obj i.as)) hi)
          (congrArg (fun H ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue H (A.obj j.as)) hj)) =
      (R.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hj)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramMixedHom (A.map (homOfLE hij)) F G := by
  subst F
  subst G
  simp only [eqToHom_refl, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalCocartesianTransportDiagramHom_of_le A R i j hij

/-- 実際の分類 prism の対角評価の混合 Hom も、元の固定成分の前合成に定値。 -/
lemma cocartesianTransportHomCutSimplex_fixedMixedHom
    {C : Type u} [Category.{u} C] (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : t i = 0) (hj : t j = 1)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (σ.obj j))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (σ.obj j)))) _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent F G (σ.obj j)) b) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex F G σ s.val.down t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj)) =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (F.val.map (σ.map (homOfLE hij)))).app
        (G.val.obj (σ.obj j)))).app (Opposite.op ⦋0⦌) b.down) := by
  have h := diagonalCocartesianTransportDiagramHom_normalized (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramSimplexBase σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex s.val.down t) ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_zero s.val.down t i hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentRightIntervalCutSimplex_obj_one s.val.down t j hj)
  exact h.trans (cocartesianHomSourceComponent_cutMixedHom (σ.map (homOfLE hij))
    F G b s t i j hi hj)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
