module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：関手同型のホモトピー圏での成分と実際の頂点評価の一致。
方針：ホモトピー評価関手を頂点で評価すると単体的評価のホモトピー圏の射となる。
規約：指定された同型そのものの成分を同定する。
使われ方：普遍余単位の成分の可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：ホモトピー評価の指定頂点成分は単体的な頂点評価のホモトピー圏への作用。
方針：頂点と辺の生成元で関手を比較する。
規約：始域と標的の充填条件は不要。
使われ方：関手同型の成分と頂点同型の像を同定する。 -/
lemma functorHomotopyEvaluation_evaluate {K X : SSet.{u}} (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation K X ⋙ (evaluation (hoFunctor.obj K) (hoFunctor.obj X)).obj
      (SSet.HomotopyCategory.mk k) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).toFunctor := by
  refine SSet.Truncated.HomotopyCategory.functor_ext (fun F ↦ ?_) ?_
  · change SSet.HomotopyCategory.mk (F.app _ (𝟙 _) k) =
      SSet.HomotopyCategory.mk (F.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 0))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  · intro f g e
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorHomotopyEvaluation]
    dsimp only [SSet.mapHomotopyCategory]
    have hp := SSet.Truncated.HomotopyCategory.BinaryProduct.inverse_map_mkHom_homMk_id
      (X := (truncation 2).obj ((ihom K).obj X)) (Y := (truncation 2).obj K) e k
    have hl := congrArg (fun j :
        SSet.Truncated.HomotopyCategory.mk (f, k) ⟶
          SSet.Truncated.HomotopyCategory.mk (g, k) ↦
      (SSet.Truncated.mapHomotopyCategory ((truncation 2).map
        ((β_ ((ihom K).obj X) K).hom ≫ (ihom.ev K).app X))).map j) hp
    let ev : (truncation 2).obj ((ihom K).obj X) ⊗ (truncation 2).obj K ⟶
        (truncation 2).obj X :=
      (truncation 2).map ((β_ ((ihom K).obj X) K).hom ≫ (ihom.ev K).app X)
    let a := e.tensor (SSet.Truncated.Edge.id (X := (truncation 2).obj K) k)
    have heq : (a.map ev).edge =
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))).edge := by
      change e.edge.app _ (𝟙 _) (K.σ 0 k) =
        e.edge.app _ (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1)
      have hk : K.σ 0 k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1 := by
        simpa only [SimplicialObject.σ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback k (SimplexCategory.σ (n := 0) 0))
      exact congrArg (fun z : K _⦋1⦌ ↦ e.edge.app _ (𝟙 _) z) hk
    have ha := SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk (a.map ev)
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))) heq
    obtain ⟨hx, hy, he⟩ := (Arrow.mk_eq_mk_iff _ _).mp ha
    exact hl.trans he

/-- 概要：関手同型の実際の成分は頂点評価による同じ同型の像。
方針：ホモトピー評価の成分の関手を単体的評価の関手へ同定する。
規約：端点の評価の等式による移送を明示する。
使われ方：普遍余単位の成分を計算する。 -/
lemma FunctorIso.app_eq_evaluate {K X : SSet.{u}}
    [Quasicategory K] [Quasicategory X] {f g : K ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (k : K _⦋0⦌) :
    e.app k =
      (eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k f))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k) ≪≫
      eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k g)) := by
  have h := Functor.congr_hom (functorHomotopyEvaluation_evaluate (X := X) k) e.hom
  apply Iso.ext
  simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map, eqToHom_app] using h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (app_eq_evaluate)


/-- 概要：関手同型の実際の頂点成分は逆同型を保つ。
方針：頂点評価による同型の像の反転を使う。
規約：既存の成分の選択を保持する。
使われ方：普遍単位の成分と余単位の逆を結ぶ。 -/
lemma FunctorIso.app_symm {K X : SSet.{u}} [Quasicategory K] [Quasicategory X]
    {f g : K ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app e.symm k = (e.app k).symm := by
  rw [FunctorIso.app_eq_evaluate, FunctorIso.app_eq_evaluate]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_symm, Iso.trans_symm, Iso.trans_assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso export _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso (app_symm)


end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
