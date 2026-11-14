module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteImage

/-!
# 同じ U の元の代数頂点の全ホモロジー比較

概要：既存 U の値の全ホモロジーを元の代数の底のホモロジーへ同定する。
方針：元の頂点比較と同じ実 augmentation の擬同型を通す。
規約：元の U と全整数次数を保持する。
使われ方：離散性から元の底のホモロジー支持を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def cAlgUnderlyingHomologyIso (B : (operad A).Algebra) (i : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A i
      ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌) (cAlgVertex A B)) ≅ B.carrier.homology i := by
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory
    ((truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).mapIso
      (cAlgForgetDerived_valueVertexIso A B)
  have h := cAlgForgetDerivedValueAugmentation_quasiIso A B
  have e' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyIso A i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (cAlgForgetDerivedValue A B))
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology A i (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (cAlgForgetDerivedValue A B)) ≅
    (cAlgForgetDerivedValue A B).val.homology i at e'
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor A i).mapIso e ≪≫ e' ≪≫
    asIso (HomologicalComplex.homologyMap (cAlgForgetDerivedValueAugmentation A B) i)

lemma cAlgVertex_underlyingDisc_iff (B : (operad A).Algebra) :
    cAlgUnderlyingDisc A (cAlgVertex A B) ↔
      ∀ i : ℤ, i ≠ 0 → IsZero (B.carrier.homology i) := by
  constructor
  · intro h i hi
    exact (h i hi).of_iso (cAlgUnderlyingHomologyIso A B i).symm
  · intro h i hi
    exact (h i hi).of_iso (cAlgUnderlyingHomologyIso A B i)

lemma cAlgVertex_underlyingDisc_isLE (B : (operad A).Algebra)
    (h : cAlgUnderlyingDisc A (cAlgVertex A B)) : B.carrier.IsLE 0 := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (cAlgVertex_underlyingDisc_iff A B).mp h i (ne_of_gt hi)

lemma cAlgVertex_underlyingDisc_isGE (B : (operad A).Algebra)
    (h : cAlgUnderlyingDisc A (cAlgVertex A B)) : B.carrier.IsGE 0 := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (cAlgVertex_underlyingDisc_iff A B).mp h i (ne_of_lt hi)

lemma cAlgVertex_underlyingDisc (B : (operad A).Algebra)
    [B.carrier.IsLE 0] [B.carrier.IsGE 0] : cAlgUnderlyingDisc A (cAlgVertex A B) := by
  apply (cAlgVertex_underlyingDisc_iff A B).mpr
  intro i hi
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact B.carrier.exactAt_of_isGE 0 i hi
  · exact B.carrier.exactAt_of_isLE 0 i hi

end SerrePositivity.EInfinity.BarrattEccles

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.3.17" (partial := component) "仮定：可換環 R 上の実 Barratt–Eccles 代数とその CAlg_R 頂点（Lean が強い：この模型と離散性の場合）。結論：底の導来像が離散であることと台の全非零次数のホモロジー消滅が同値となる（基礎対象による離散性の部分に一致）。代数の ∞ 写像空間の零切断性と一般 k の比較は含まれない。"] _root_.SerrePositivity.EInfinity.BarrattEccles.cAlgVertex_underlyingDisc_iff
