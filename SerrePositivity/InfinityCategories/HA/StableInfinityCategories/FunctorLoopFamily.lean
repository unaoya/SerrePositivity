module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopSquareCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap

/-!
概要：元の実 loop 四角形の族を関手圏の全単体の族へ送る。
方針：後合成と内部 Hom の交換で同じ四角形を点ごとに作用させる。
規約：安定性を先取りせず、選んだ loop の切断を保持する。
使われ方：一般零角の図式族の回転と loop 同値の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：元の loop 四角形を関手の全単体へ後合成する生の族。
方針：関手変数と四角形変数を交換する。
規約：まだ loop の頂点条件への持ち上げは行わない。
使われ方：関手圏の実 loop 切断の構成。 -/
def functorLoopSquareFamily (K : SSet.{u}) {X : SSet.{u}} (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) :
    (ihom K).obj X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj ((ihom K).obj X) :=
  (ihom K).map (s ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K (Δ[1] ⊗ Δ[1]) X).hom

/-- 概要：関手変数の評価は元の同じ loop 四角形を回収する。
方針：内部 Hom の交換と点での評価の可換性を使う。
規約：全単体での実等式。使われ方：loop の点ごとの普遍性。 -/
lemma functorLoopSquareFamily_evaluate {K X : SSet.{u}}
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (k : K _⦋0⦌) :
    functorLoopSquareFamily K s ≫ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ s ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι := by
  rw [functorLoopSquareFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate]
  rfl

/-- 概要：四角形の各角の評価は元の loop 評価への後合成である。
方針：交換した全関手の同じ角を計算する。
規約：関手変数の全単体作用を保持する。
使われ方：関手圏の loop 切断と loop 関手の同値性。 -/
lemma functorLoopSquareFamily_corner {K X : SSet.{u}}
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (i j : Fin 2) :
    functorLoopSquareFamily K s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
      (ihom K).map (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X i j) := by
  let g : X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
    s ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι
  change ((ihom K).map g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso K (Δ[1] ⊗ Δ[1]) X).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) =
    (ihom K).map (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro k
  change (g.app e (v.app e (α ≫ 𝟙 e) k)).app e (𝟙 e)
        (((Δ[1] : SSet.{u}) ⊗ Δ[1]).map α
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i,
            stdSimplex.obj₀Equiv.symm j) n.unop.len)) =
    (g.app e (v.app e α k)).app e (𝟙 e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i,
          stdSimplex.obj₀Equiv.symm j) e.unop.len)
  rw [Category.comp_id]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback
    (X := (Δ[1] : SSet.{u}) ⊗ Δ[1])
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) α.unop
  exact congrArg (fun b ↦ (g.app e (v.app e α k)).app e (𝟙 e) b) hc

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
