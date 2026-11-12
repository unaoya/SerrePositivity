module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：終端辺を点ごとに可逆に送る、任意パラメータ付きの最後の外ホーンを充填する。
方針：パラメータを curry し、関手 ∞ 圏の辺の点ごとの可逆性を使う。
規約：パラメータの充填性は不要で、外ホーンの次元は二以上。
使われ方：相対指数の cartesian な辺を、元の図式の可逆化条件から構成する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：内部 Hom の任意の一単体は全ての評価で可逆なら可逆。
方針：両端の頂点を実際の関手で表し、指定された辺の点ごとの判定を使う。
規約：端点の関手は存在することを使うだけで、辺自体は変えない。
使われ方：外ホーンの族を関手 ∞ 圏で充填する。 -/
lemma functorSimplex_isInvertible_of_pointwise {T D : SSet.{u}} [Quasicategory D]
    (e : ((ihom T).obj D) _⦋1⦌)
    (he : ∀ x : T _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := D) x).app (Opposite.op ⦋1⦌) e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e) := by
  obtain ⟨f, hf⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T D).surjective (((ihom T).obj D).δ 1 e)
  obtain ⟨g, hg⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv T D).surjective (((ihom T).obj D).δ 0 e)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f = _ at hf
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g = _ at hg
  let a : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) := ⟨e, hf.symm, hg.symm⟩
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt a).2 (by
    intro x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (by rfl)).2 (he x))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show a.edge = e from rfl)).1 ha

/-- 概要：最後の外ホーンの族は指定終端辺を各パラメータ頂点で可逆に送れば充填できる。
方針：パラメータで curry し、関手 ∞ 圏で可逆終端辺を持つ外ホーンを充填する。
規約：T は任意、D は quasicategory。全てのパラメータで元の族に厳密に一致する。
使われ方：cartesian 辺の最後の外ホーンの持ち上げ。 -/
lemma exists_kanFinalHornFamily_extension {T D : SSet.{u}} [Quasicategory D] (n : ℕ)
    (F : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⊗ T ⟶ D)
    (he : ∀ x : T _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (F.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))) :
    ∃ L : (Δ[n + 2] : SSet.{u}) ⊗ T ⟶ D,
      ((horn (n + 2) (Fin.last (n + 2))).ι ▷ T) ≫ L = F := by
  let A := (horn (n + 2) (Fin.last (n + 2)) : SSet.{u})
  let G : A ⟶ (ihom T).obj D := curry ((β_ T A).hom ≫ F)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (G.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) := by
    apply functorSimplex_isInvertible_of_pointwise
    intro x
    exact he x
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge _ hc n G rfl
  let L : (Δ[n + 2] : SSet.{u}) ⊗ T ⟶ D := (β_ Δ[n + 2] T).hom ≫ uncurry H
  refine ⟨L, ?_⟩
  apply (cancel_epi (β_ T A).hom).1
  have hs : (β_ T A).hom ≫ (((horn (n + 2) (Fin.last (n + 2))).ι ▷ T) ≫ L) =
      (T ◁ (horn (n + 2) (Fin.last (n + 2))).ι) ≫ uncurry H := rfl
  rw [hs, ← uncurry_natural_left, hH, uncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
