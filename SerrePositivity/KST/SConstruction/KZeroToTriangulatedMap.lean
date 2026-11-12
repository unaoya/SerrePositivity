module
public import SerrePositivity.KST.SConstruction.TriangulatedNerveDescent
public import SerrePositivity.KST.SConstruction.KZeroFundamentalGroup
public import SerrePositivity.KST.SConstruction.FundamentalLoopHom

/-! # 実際の零次 K 群から三角圏 K₀ への逆向き準同型
概要：元の対象類から作った Kan 境界上の写像を、実際の零次群の加法準同型へ移す。
方針：基本群とホモトピー圏の loop の同値を使い、一対象亜群の射として評価する。
規約：順方向との逆律は別途必要。使われ方：π₀ K と三角圏 K₀ の同型の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 可換群の一対象圏への関手は、既存の基本群からの加法準同型を与える。 -/
def kanLoopSingleObjAddHom (B : SSet.{u}) [KanComplex B] (b : B _⦋0⦌)
    (A : Type u) [AddCommGroup A]
    (F : hoFunctor.obj B ⥤ AsSmall.{u} (SingleObj (Multiplicative A))) :
    Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 b) →+ A where
  toFun a := (F.map (fundamentalLoopHomEquiv B b a.toMul)).down.toAdd
  map_zero' := by
    change (F.map (fundamentalLoopHomEquiv B b 1)).down.toAdd = 0
    rw [fundamentalLoopHomEquiv_one, CategoryTheory.Functor.map_id]
    rfl
  map_add' a c := by
    change (F.map (fundamentalLoopHomEquiv B b (a.toMul * c.toMul))).down.toAdd = _
    rw [fundamentalLoopHomEquiv_mul, CategoryTheory.Functor.map_comp]
    change (F.map (fundamentalLoopHomEquiv B b c.toMul)).down.toAdd +
      (F.map (fundamentalLoopHomEquiv B b a.toMul)).down.toAdd = _
    exact add_comm _ _

/-- 元の境界定数一次単体の類は、同じ loop 辺の関手による評価で計算する。 -/
lemma kanLoopSingleObjAddHom_mk (B : SSet.{u}) [KanComplex B] (b : B _⦋0⦌)
    (A : Type u) [AddCommGroup A]
    (F : hoFunctor.obj B ⥤ AsSmall.{u} (SingleObj (Multiplicative A)))
    (s : B.PtSimplex 1 b) :
    kanLoopSingleObjAddHom B b A F (Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
      (F.map (SSet.Truncated.HomotopyCategory.homMk (fundamentalLoopEdge s))).down.toAdd := rfl

/-- 元の境界定数一次単体の逆の類は、同じ loop 辺の評価の負で計算する。 -/
lemma kanLoopSingleObjAddHom_inv_mk (B : SSet.{u}) [KanComplex B] (b : B _⦋0⦌)
    (A : Type u) [AddCommGroup A]
    (F : hoFunctor.obj B ⥤ AsSmall.{u} (SingleObj (Multiplicative A)))
    (s : B.PtSimplex 1 b) :
    kanLoopSingleObjAddHom B b A F (Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)⁻¹) =
      -(F.map (SSet.Truncated.HomotopyCategory.homMk (fundamentalLoopEdge s))).down.toAdd := by
  change kanLoopSingleObjAddHom B b A F (-Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) = _
  rw [map_neg, kanLoopSingleObjAddHom_mk]

/-- 元の辺と二単体の K₀ 関係から作る、実際の BF 零次群から三角圏 K₀ への準同型。 -/
def kZeroToTriangulatedMap (X : StableModel.{u}) :
    Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) →+
      TriangulatedK0 (hoFunctor.obj X.carrier) :=
  (kanLoopSingleObjAddHom ((boundaryKanRealizationFunctor 0).obj X).right
    ((boundaryKanRealizationFunctor 0).obj X).basepoint (TriangulatedK0 (hoFunctor.obj X.carrier))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X))).comp
      (kZeroFundamentalGroupEquiv X).toMonoidHom.toAdditive

/-- 逆向き準同型は、元の基本群の loop を実際の Kan 境界上の関手で評価して計算する。 -/
lemma kZeroToTriangulatedMap_apply (X : StableModel.{u})
    (a : Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0)) :
    kZeroToTriangulatedMap X a =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X)).map
        (fundamentalLoopHomEquiv ((boundaryKanRealizationFunctor 0).obj X).right
          ((boundaryKanRealizationFunctor 0).obj X).basepoint
          (kZeroFundamentalGroupEquiv X a.toMul))).down.toAdd := rfl

/-- 元の対象 K 類の逆向きの像は、元の Kan 辺の評価の負で計算できる。 -/
lemma kZeroToTriangulatedMap_object_formula (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    kZeroToTriangulatedMap X (objectKClass X ((sOneComparison X.carrier).app _ e)) =
      -((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X)).map
        (SSet.Truncated.HomotopyCategory.homMk
          (fundamentalLoopEdge (objectBoundaryEdge X e)))).down.toAdd := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TruncationsAndPostnikovTowers.fundamentalNerveUntranspose (boundaryKanTriangulatedMap X)
  let h := kanLoopSingleObjAddHom ((boundaryKanRealizationFunctor 0).obj X).right
    ((boundaryKanRealizationFunctor 0).obj X).basepoint
    (TriangulatedK0 (hoFunctor.obj X.carrier)) F
  have hc := congrArg (fun a => h (Additive.ofMul a)) (objectBoundaryEdge_objectKClass X e)
  exact hc.trans (kanLoopSingleObjAddHom_inv_mk _ _ _ F (objectBoundaryEdge X e))

end SerrePositivity.KST.SConstruction
