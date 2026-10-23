module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCellCospan
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativeFunctor
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramColimitCone

/-!
概要：同じ二辺・共有頂点で、元の局所 Hom と分類先の cospan の比較を作る。
方針：同じ底上の cospan に源・標的の既存の反変関手を適用する。
規約：成分は元の零・一次元の分類 Hom 作用であり、共有頂点は一つだけ。
使われ方：二次元 Segal 比較の成分同値と同じ両脚の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二辺と同じ共有頂点の全局所 Hom の core の cospan。 -/
def cocartesianTwoSimplexLocalSource : WalkingCospan ⥤ SSet.{u + 1} :=
  cospan
    ((SSet.uliftFunctor.{u + 1, u}).map
      (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
        (cocartesianTwoSimplexSharedToFirst k))))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
        (cocartesianTwoSimplexSharedToSecond k))))

/-- 同じ二辺と共有頂点へ分類図式を制限した区間 Hom の cospan。 -/
def cocartesianTwoSimplexLocalTarget : WalkingCospan ⥤ SSet.{u + 1} :=
  cospan (uliftOverMorphism (cocartesianTwoSimplexSharedToFirst k)).op
      (uliftOverMorphism (cocartesianTwoSimplexSharedToSecond k)).op ⋙
    intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 同じ cospan の各対象での比較は、元の局所分類 Hom 作用そのもの。 -/
def cocartesianTwoSimplexLocalComparison (j : WalkingCospan) :
    (cocartesianTwoSimplexLocalSource k p q).obj j ⟶
      (cocartesianTwoSimplexLocalTarget k p q).obj j := by
  cases j with
  | none => exact cocartesianLocalHomComparison (cocartesianTwoSimplexSharedCell k) p q
  | some j =>
    cases j with
    | left => exact cocartesianLocalHomComparison (cocartesianTwoSimplexFirstCell k) p q
    | right => exact cocartesianLocalHomComparison (cocartesianTwoSimplexSecondCell k) p q

instance cocartesianTwoSimplexLocalSource_kanComplex (j : WalkingCospan) :
    KanComplex ((cocartesianTwoSimplexLocalSource k p q).obj j) := by
  cases j with
  | none =>
    change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched
        (nerveMap (cocartesianTwoSimplexSharedCell k))).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched
        (nerveMap (cocartesianTwoSimplexSharedCell k))).obj q)))
    infer_instance
  | some j =>
    cases j with
    | left =>
      change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianTwoSimplexFirstCell k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianTwoSimplexFirstCell k))).obj q)))
      infer_instance
    | right =>
      change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianTwoSimplexSecondCell k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianTwoSimplexSecondCell k))).obj q)))
      infer_instance

instance cocartesianTwoSimplexLocalTarget_kanComplex (j : WalkingCospan) :
    KanComplex ((cocartesianTwoSimplexLocalTarget k p q).obj j) := by
  dsimp only [cocartesianTwoSimplexLocalTarget, CategoryTheory.Functor.comp_obj,
    intervalDiagramOverFunctor]
  infer_instance

/-- 同じ二辺と同じ共有頂点の元の全 Hom 比較は、三成分とも同値。 -/
lemma cocartesianTwoSimplexLocalComparison_isQCatEquivalence (j : WalkingCospan) :
    IsQCatEquivalence (cocartesianTwoSimplexLocalComparison k p q j) := by
  cases j with
  | none => exact cocartesianLocalHomComparison_zeroCell_isQCatEquivalence _ p q
  | some j =>
    cases j with
    | left => exact cocartesianLocalHomComparison_oneCell_isQCatEquivalence _ p q
    | right => exact cocartesianLocalHomComparison_oneCell_isQCatEquivalence _ p q

end SerrePositivity.InfinityCategories
