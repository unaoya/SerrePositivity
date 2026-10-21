module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldCellCospan
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackNativeFunctor
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramColimitCone

/-!
概要：同じ最初の辺・尾部・共有頂点で、元の局所 Hom と分類先の cospan の比較を作る。
方針：同じ底上の cospan に源・標的の既存の反変関手を適用する。
規約：成分は元の元の各次元の分類 Hom 作用であり、共有頂点は一つだけ。
使われ方：高次元 Segal 比較の成分同値と同じ両脚の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二辺と同じ共有頂点の全局所 Hom の core の cospan。 -/
def cocartesianScaffoldLocalSource : WalkingCospan ⥤ SSet.{u + 1} :=
  cospan
    ((SSet.uliftFunctor.{u + 1, u}).map
      (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
        (cocartesianScaffoldSharedToFirst n k))))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
        (cocartesianScaffoldSharedToTail n k))))

/-- 同じ最初の辺と尾部と共有頂点へ分類図式を制限した区間 Hom の cospan。 -/
def cocartesianScaffoldLocalTarget : WalkingCospan ⥤ SSet.{u + 1} :=
  cospan (uliftOverMorphism (cocartesianScaffoldSharedToFirst n k)).op
      (uliftOverMorphism (cocartesianScaffoldSharedToTail n k)).op ⋙
    intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)

/-- 同じ cospan の各対象での比較は、元の局所分類 Hom 作用そのもの。 -/
def cocartesianScaffoldLocalComparison (j : WalkingCospan) :
    (cocartesianScaffoldLocalSource n k p q).obj j ⟶
      (cocartesianScaffoldLocalTarget n k p q).obj j := by
  cases j with
  | none => exact cocartesianLocalHomComparison (cocartesianScaffoldSharedCell n k) p q
  | some j =>
    cases j with
    | left => exact cocartesianLocalHomComparison (cocartesianScaffoldFirstCell n k) p q
    | right => exact cocartesianLocalHomComparison (cocartesianScaffoldTailCell n k) p q

instance cocartesianScaffoldLocalSource_kanComplex (j : WalkingCospan) :
    KanComplex ((cocartesianScaffoldLocalSource n k p q).obj j) := by
  cases j with
  | none =>
    change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched
        (nerveMap (cocartesianScaffoldSharedCell n k))).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched
        (nerveMap (cocartesianScaffoldSharedCell n k))).obj q)))
    infer_instance
  | some j =>
    cases j with
    | left =>
      change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianScaffoldFirstCell n k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianScaffoldFirstCell n k))).obj q)))
      infer_instance
    | right =>
      change KanComplex ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianScaffoldTailCell n k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched
          (nerveMap (cocartesianScaffoldTailCell n k))).obj q)))
      infer_instance

instance cocartesianScaffoldLocalTarget_kanComplex (j : WalkingCospan) :
    KanComplex ((cocartesianScaffoldLocalTarget n k p q).obj j) := by
  dsimp only [cocartesianScaffoldLocalTarget, CategoryTheory.Functor.comp_obj,
    intervalDiagramOverFunctor]
  infer_instance

/-- 尾部の帰納仮定から、同じ最初の辺・尾部・共有頂点の三成分比較は同値。 -/
lemma cocartesianScaffoldLocalComparison_isQCatEquivalence
    (htail : IsQCatEquivalence
      (cocartesianLocalHomComparison (cocartesianScaffoldTailCell n k) p q))
    (j : WalkingCospan) :
    IsQCatEquivalence (cocartesianScaffoldLocalComparison n k p q j) := by
  cases j with
  | none => exact cocartesianLocalHomComparison_zeroCell_isQCatEquivalence _ p q
  | some j =>
    cases j with
    | left => exact cocartesianLocalHomComparison_oneCell_isQCatEquivalence _ p q
    | right => exact htail

end SerrePositivity.InfinityCategories
