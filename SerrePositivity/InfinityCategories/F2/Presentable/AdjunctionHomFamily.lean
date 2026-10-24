module

public import SerrePositivity.InfinityCategories.F2.Presentable.AdjunctionCosliceFibers
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftClassificationComparisonIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceCommaEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.MappingArrowCriterion

/-!
概要：随伴の共変 Hom 対応を全関手の自然同型として構成する。
方針：同じ底上の coslice–comma 比較を分類し、元の Hom 関手へ戻す。
規約：対象ごとの同値族から自然性を推測せず、実際の全空間の射を用いる。
使われ方：右随伴の accessibility と Hom 族の余極限保存判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の Hom の制限は固定始点 comma の全分類関手と自然同型。
方針：coslice の底変換を分類し、底上の標準比較を全自然に可逆化する。
規約：元の共変表現可能関手と元の関手 G を保持する。
使われ方：随伴の Hom 族の標的表示。 -/
def covariantHomCommaClassificationIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (x : X _⦋0⦌) :
    FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map G ≫ covariantRepresentableInfinity x)
      (leftStraighteningInfinityDiagram (F1B.unitCommaFiberProjection G x)) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have : LeftFibration (pullback.snd p G) :=
    ⟨leftFibrations.pullback_snd p G (LeftFibration.mem (p := p))⟩
  have hf := (leftFibration_precompositionEquivalence_iff_fibers
    (pullback.snd p G) (F1B.unitCommaFiberProjection G x)
    (cosliceCommaComparison G x) (cosliceCommaComparison_projection G x)).mp
      (cosliceCommaComparison_isQCatEquivalence G x).isPrecompositionEquivalence
  exact ((Compact.covariantRepresentableInfinity_cosliceIso x).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map G)) ≪≫
      leftStraighteningInfinityDiagram_baseChangeIso p G ≪≫
        leftClassificationComparisonIso _ _ _ _ hf

/-- 概要：各点で同値な coherent な矢印比較の固定始点分類は自然同型。
方針：元の fiber 比較を区間比較と同定し、全分類射の可逆性へ戻す。
規約：始域と終域の全 Hom 関手を比較する。
使われ方：随伴の共変 Hom 族の比較。 -/
def mappingArrowHomFamilyIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (q : MappingArrowComparison F G)
    (hq : q.IsPointwiseEquivalence) (x : X _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity (F.app (Opposite.op ⦋0⦌) x))
      ((SSet.uliftFunctor.{u + 1, u}).map G ≫ covariantRepresentableInfinity x) := by
  have hf : ∀ y : Y _⦋0⦌, IsQCatEquivalence (vertexFiberMap
      (sliceUnderProjection (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
      (F1B.unitCommaFiberProjection G x) (adjunctionCosliceComparison q x)
      (adjunctionCosliceComparison_projection q x) y) := by
    intro y
    have hi := (qCatEquivalenceOfIso (F1B.unitCommaFiberIntervalIso G x y)).isQCatEquivalence
    apply hi.cancel_right
    change IsQCatEquivalence (_ ≫ F1B.unitCommaFiberToInterval G x y)
    rw [adjunctionCosliceComparison_fiber]
    exact (cosliceFiberToIntervalMappingSpace_isQCatEquivalence _ y).comp
      (hq x y).isQCatEquivalence
  exact Compact.covariantRepresentableInfinity_cosliceIso _ ≪≫
    leftClassificationComparisonIso _ _ _ _ hf ≪≫ (covariantHomCommaClassificationIso G x).symm

/-- 概要：指定した随伴は元の共変 Hom 関手の全自然な同型を与える。
方針：随伴の単位の coherent な矢印比較を全分類する。
規約：モデル構造や追加の Hom 自然性条件を仮定しない。
使われ方：右随伴の accessibility の証明。 -/
def adjunctionCovariantHomIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity (F.app (Opposite.op ⦋0⦌) x))
      ((SSet.uliftFunctor.{u + 1, u}).map G ≫ covariantRepresentableInfinity x) :=
  mappingArrowHomFamilyIso (MappingArrowComparison.ofUnitHom a.unitHom)
    (MappingArrowComparison.ofUnitHom_isPointwiseEquivalence a.unitHom
      a.unitMappingSpaceCondition) x

end SerrePositivity.InfinityCategories.F2.Presentable
