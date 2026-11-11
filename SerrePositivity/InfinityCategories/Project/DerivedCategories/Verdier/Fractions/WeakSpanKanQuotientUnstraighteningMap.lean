module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.WeakSpanKanQuotientDescent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningBaseChange

/-!
概要：元の商降下同型から、単体圏上の同じ小さい unstraightening を商上へ送る。
方針：指定降下同型の全変換空間での実像と、既存の厳密な底変換を合成する。
規約：元の marked span 全族からの写像はまだ構成しない。Ind-S (5) の単位を待つ。
使われ方：K-B-S の全族単位を受け取った後に使う、同じ商図式への全空間比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：指定された商降下同型を使う、同じ小さい unstraightening の全空間比較。
方針：降下同型の逆を元の全変換空間で作用させ、同じ底 q へ写す。
規約：値ごとの同値を独立に選び直さない。
使われ方：K-B-S の元の全族単位に後合成する実比較射。 -/
def weakSpanKanQuotientSimplexUnstraighteningMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallUnstraighteningFunctorHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram_simplexIso h x).symm.hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMap
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj ≫ q.hom) rfl

/-- 概要：同じ全空間比較は元の初頂点写像と商 q を厳密に被覆する。
方針：指定全変換の底保存と既存の小さい底変換の射影式を使う。
規約：底の可換性を自然同型だけに弱めない。
使われ方：K-B-S の厳密な底条件を同じ実全空間射について保持する。 -/
theorem weakSpanKanQuotientSimplexUnstraighteningMap_projection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap h x ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj ≫ q.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningMap_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallUnstraighteningFunctorHom_projection]

/-- 概要：元の単体圏上の全族単位を受け、同じ商図式への全空間射を作る。
方針：供給された単位へ同じ指定降下同型の実比較を後合成する。
規約：単位に条件付き。元の marked span 全族への降下や恒等点比較はまだ主張しない。
使われ方：Ind-S (5) の供給を K-B-S の次の段へ接続する。 -/
def weakSpanKanQuotientSimplexFamilyMap
    (f : pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x)) :=
  f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap h x

/-- 概要：供給された単位の厳密な底保存を同じ商上の全族射へ移す。
方針：元の単位の射影式へ指定降下比較の射影式を合成する。
規約：単体圏引き戻し上での条件付き結果。元の全族の供給完了とは数えない。
使われ方：Ind-S (5) の後の K-B-S の厳密な底条件。 -/
theorem weakSpanKanQuotientSimplexFamilyMap_projection
    (f : pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x))
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanCoherentDiagram i x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap h x f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientDiagram h x) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanSimplexProjection i x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj ≫ q.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap_projection, ← Category.assoc, hf]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexFamilyMap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexFamilyMap_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap_projection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexUnstraighteningMap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexUnstraighteningMap_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexFamilyMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexFamilyMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexUnstraighteningMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientSimplexUnstraighteningMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap.eq_1
