module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianPrismBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap

/-!
概要：cocartesian な辺を頂点とする区間からの関手の全部分複体。
方針：区間の辺の相対外側ホーン充填条件で頂点を選ぶ。
規約：始点と基底の区間全体を保持する。
使われ方：Kerodon §5.1.4（Tag 01U9）・§7.1.5（Tag 02WE） の coherent な輸送。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：区間からの関手の頂点は評価した二端点間の辺を与える。
方針：Yoneda による一次単体表示の両端を評価で計算する。
規約：元の単体集合に quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の基底の辺の持ち上げ。 -/
def intervalFunctorVertexTypedEdge {E : SSet.{u}} (v : ((ihom (Δ[1] : SSet.{u})).obj E) _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj E)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) v) where
  edge := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v
  src_eq := by
    obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] E).surjective v
    change E.δ 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
      ← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp]
    exact congrArg (f.app (Opposite.op ⦋0⦌)) (by decide)
  tgt_eq := by
    obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] E).surjective v
    change E.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
      ← stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_comp]
    exact congrArg (f.app (Opposite.op ⦋0⦌)) (by decide)

/-- 概要：区間からの関手の頂点が cocartesian な辺を表す条件。
方針：頂点が表す一次単体の相対ホーン充填条件を取る。
規約：端点の表示は辺から定める。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の選択。 -/
def IsCocartesianHornPathVertex {E B : SSet.{u}} (p : E ⟶ B)
    (v : ((ihom (Δ[1] : SSet.{u})).obj E) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (intervalFunctorVertexTypedEdge v)

/-- 概要：cocartesian な辺を頂点とする path の全部分複体。
方針：区間からの関手単体集合の頂点条件で制限する。
規約：高次単体には全頂点の条件を要求する。
使われ方：Kerodon §5.1.4（Tag 01U9） の coherent な輸送の空間。 -/
def cocartesianPathSpace {E B : SSet.{u}} (p : E ⟶ B) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj E) (IsCocartesianHornPathVertex p) : SSet.{u})

/-- 概要：cocartesian な path を区間からの関手へ含める。
方針：全部分複体の包含を使う。
規約：全次数で単射。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の評価。 -/
def cocartesianPathSpaceι {E B : SSet.{u}} (p : E ⟶ B) :
    cocartesianPathSpace p ⟶ (ihom (Δ[1] : SSet.{u})).obj E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCocartesianHornPathVertex p)).ι

/-- 概要：cocartesian な path から始点と基底の path への射。
方針：始点評価と p による後合成を引き戻しへ合わせる。
規約：基底の path の始点は p による始点の像。
使われ方：Kerodon §5.1.4（Tag 01U9）・§7.1.5（Tag 02WE） の始点を固定した輸送の持ち上げ。 -/
noncomputable def cocartesianPathSpaceSource {E B : SSet.{u}} (p : E ⟶ B) :
    cocartesianPathSpace p ⟶
      pullback p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :=
  pullback.lift
    (cocartesianPathSpaceι p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (cocartesianPathSpaceι p ≫ (ihom (Δ[1] : SSet.{u})).map p) rfl

/-- 概要：cocartesian な path の始点と基底の射の第一射影は始点評価。
方針：pullback の持ち上げの第一射影を計算する。
規約：p のファイブレーション性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の始点の固定。 -/
lemma cocartesianPathSpaceSource_fst {E B : SSet.{u}} (p : E ⟶ B) :
    cocartesianPathSpaceSource p ≫
      pullback.fst p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        cocartesianPathSpaceι p ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
  pullback.lift_fst _ _ _

/-- 概要：cocartesian な path の始点と基底の射の第二射影は基底への後合成。
方針：pullback の持ち上げの第二射影を計算する。
規約：p のファイブレーション性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の基底の固定。 -/
lemma cocartesianPathSpaceSource_snd {E B : SSet.{u}} (p : E ⟶ B) :
    cocartesianPathSpaceSource p ≫
      pullback.snd p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
        cocartesianPathSpaceι p ≫ (ihom (Δ[1] : SSet.{u})).map p :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
