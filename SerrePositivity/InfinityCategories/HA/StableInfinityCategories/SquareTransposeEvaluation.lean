module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 四角形の転置と対角頂点の評価

概要：図式の転置は対角の二頂点におけるホモトピー圏の射の評価を保つ。
方針：前合成と評価の交換式で、座標交換が対角頂点を固定することを使う。
規約：始点・終点のどちらにも適用する。使われ方：転置した suspension の標準比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：対角頂点での評価の前の転置は、元の評価と同じ単体的な射になる。
方針：前合成と評価の交換式を使う。
規約：値域への仮定なし。使われ方：h の射の評価の転置不変性。 -/
lemma squareTranspose_evaluation (X : SSet.{u}) (i : Fin 2) :
    (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i i) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i i) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 概要：四角形のホモトピー圏の射の対角頂点の評価は、転置で変わらない。
方針：二回の h の射の像をまとめ、単体的な評価の等号で照合する。
規約：値域は quasicategory。使われ方：標準比較の始点と suspension 頂点の照合。 -/
lemma squareDiagramHoEvaluation_transpose {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X}
    (a : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) :
      hoFunctor.obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i i).map
      ((hoFunctor.map ((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)).toFunctor.map a) =
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i i).map a := by
  apply Arrow.mk_injective
  exact (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp
    ((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) i i)) a)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_congr_arrow (squareTranspose_evaluation X i) a)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
