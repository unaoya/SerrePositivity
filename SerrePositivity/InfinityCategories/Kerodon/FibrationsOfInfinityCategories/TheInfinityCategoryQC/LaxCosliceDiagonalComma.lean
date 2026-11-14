module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCoslice
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCosliceUncurry
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.LaxCosliceUniversal
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComma
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberExtension
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberFamilies
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FatCoconeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FatCoconeHomotopyEquiv
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FatCoconeHomotopyNaturality

/-!
概要：太い coslice の族と対角関手の固定始域 comma の族を自然に比較する。
方針：太い余錐の普遍性、円柱と自然変換の全単射、comma の普遍性を合成する。
規約：図式・頂点族・実際の自然変換を保持する。
使われ方：対角関手の cofinality を filtered な coslice の弱可縮性へ帰着する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：太い coslice と対角 comma の任意の族の全単射。
方針：固定図式の太い余錐と自然変換のデータを中間に使う。
規約：充填性の仮定なし。使われ方：単体集合の同型の構成。 -/
def laxCosliceDiagonalCommaHomEquiv {K C : SSet.{u}} (p : K ⟶ C) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) ≃ (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceHomEquiv p A).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.fatCoconeHomotopyEquiv p A).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberFamilyEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) A).symm)

/-- 概要：太い coslice の族の比較は元の余錐の頂点を保つ。
方針：comma の持ち上げの標的公式を使う。
規約：頂点族は非定値でよい。使われ方：射影を保つ同型の確認。 -/
lemma laxCosliceDiagonalCommaHomEquiv_target {A K C : SSet.{u}} {p : K ⟶ C}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget (laxCosliceDiagonalCommaHomEquiv p A f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K A ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_target _ _ _ _

/-- 概要：太い coslice の族の比較は元の余錐の円柱を保つ。
方針：comma の持ち上げの自然変換公式を使う。
規約：ホモトピー類への移行を行わない。使われ方：比較の自然性の検証。 -/
lemma laxCosliceDiagonalCommaHomEquiv_homotopy {A K C : SSet.{u}} {p : K ⟶ C}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy (laxCosliceDiagonalCommaHomEquiv p A f)).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.fatCoconeHomotopy (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed f)).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberCurry_homotopy _ _ _ _

/-- 概要：太い coslice と対角 comma の族の比較はパラメータの前合成に自然。
方針：標的族と円柱をそれぞれ前合成の公式で比較する。
規約：全ての単体集合パラメータを同時に扱う。使われ方：Yoneda による同型。 -/
lemma laxCosliceDiagonalCommaHomEquiv_naturality {A B K C : SSet.{u}} {p : K ⟶ C}
    (i : B ⟶ A) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCoslice p) :
    laxCosliceDiagonalCommaHomEquiv p B (i ≫ f) =
      i ≫ laxCosliceDiagonalCommaHomEquiv p A f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber_hom_ext
  · rw [laxCosliceDiagonalCommaHomEquiv_target, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_precomp,
      laxCosliceDiagonalCommaHomEquiv_target, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_precomp]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.assoc]
  · rw [laxCosliceDiagonalCommaHomEquiv_homotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberHomotopy_precomp,
      laxCosliceDiagonalCommaHomEquiv_homotopy]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.fatCoconeHomotopy_precomp_h (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry f)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed f) i
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.fatCoconeHomotopy, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_precomp] using! h (by
      rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_precomp]
      exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.laxCosliceUncurry_fixed (i ≫ f))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
