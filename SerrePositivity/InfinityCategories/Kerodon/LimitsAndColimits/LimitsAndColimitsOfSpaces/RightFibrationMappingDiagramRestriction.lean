module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction

/-!
概要：固定した図式への錐の比較 span を、底の同じ始点上で図式の制限に移す。
方針：既存の正規化した錐の制限を fiber に取り、射影と評価を追跡する。
規約：パラメータ形状は任意。Δ・Δᵒᵖ の比較は含めない。
使われ方：Kerodon §7.4、G8 の錐の辺全体を保持する共通 span。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 元の図式 p の錐の始点を、底上の x に固定した実空間。
一点図式の場合は rightFibrationMappingTotal と定義的に同じである。 -/
def rightFibrationMappingDiagramTotal {K E B : SSet.{u}} (r : E ⟶ B)
    (p : K ⟶ E) (x : B _⦋0⦌) : SSet.{u} :=
  vertexFiber (sliceOverProjection p ≫ r) x

/-- 概要：元の錐の始点評価を底の頂点 fiber に制限した射。
方針：射影の合成則から fiber の誘導射を作る。
規約：図式と始点を全パラメータで保持する。使われ方：辺の両端への制限の比較。 -/
def rightFibrationMappingDiagramEvaluation {K E B : SSet.{u}} (r : E ⟶ B)
    (p : K ⟶ E) (x : B _⦋0⦌) :
    rightFibrationMappingDiagramTotal r p x ⟶ vertexFiber r x :=
  vertexFiberMap (sliceOverProjection p ≫ r) r (sliceOverProjection p) rfl x

/-- 概要：図式の表示を保つ錐の制限を、同じ底の始点上で取る。
方針：既存の normalizedConeRestriction の射影公式を使う。
規約：hq は元の図式を同定する等式。使われ方：共通の辺 span の両端制限。 -/
def rightFibrationMappingDiagramRestriction {K L E B : SSet.{u}}
    (r : E ⟶ B) (p : K ⟶ E) (i : L ⟶ K) {q : L ⟶ E}
    (hq : i ≫ p = q) (x : B _⦋0⦌) :
    rightFibrationMappingDiagramTotal r p x ⟶ rightFibrationMappingDiagramTotal r q x :=
  vertexFiberMap (sliceOverProjection p ≫ r) (sliceOverProjection q ≫ r)
    (normalizedConeRestriction p i hq) (by
      rw [← Category.assoc, normalizedConeRestriction_projection]) x

/-- 錐の制限を全空間に含めると、正規化した元の制限そのものになる。 -/
lemma rightFibrationMappingDiagramRestriction_ι {K L E B : SSet.{u}}
    (r : E ⟶ B) (p : K ⟶ E) (i : L ⟶ K) {q : L ⟶ E}
    (hq : i ≫ p = q) (x : B _⦋0⦌) :
    rightFibrationMappingDiagramRestriction r p i hq x ≫
        vertexFiberι (sliceOverProjection q ≫ r) x =
      vertexFiberι (sliceOverProjection p ≫ r) x ≫ normalizedConeRestriction p i hq :=
  vertexFiberMap_ι _ _ _ _ _

/-- 概要：同じ底の始点上の錐の制限は、始点評価と厳密に可換。
方針：fiber の包含後に、既存の正規化した射影公式で比較する。
規約：全パラメータでの射の等式。使われ方：共通 span の両端の評価の一致。 -/
lemma rightFibrationMappingDiagramRestriction_evaluation {K L E B : SSet.{u}}
    (r : E ⟶ B) (p : K ⟶ E) (i : L ⟶ K) {q : L ⟶ E}
    (hq : i ≫ p = q) (x : B _⦋0⦌) :
    rightFibrationMappingDiagramRestriction r p i hq x ≫
        rightFibrationMappingDiagramEvaluation r q x =
      rightFibrationMappingDiagramEvaluation r p x := by
  apply vertexFiber_hom_ext r x
  simp only [Category.assoc, rightFibrationMappingDiagramEvaluation, vertexFiberMap_ι]
  rw [← Category.assoc, rightFibrationMappingDiagramRestriction_ι, Category.assoc,
    normalizedConeRestriction_projection]

/-- 概要：left anodyne な図式の制限は、底の同じ始点上でも自明 Kan fibration。
方針：slice 制限の自明 Kan 性、終点表示の同型、fiber の持ち上げ性を順に使う。
規約：r 自身の充填性は不要。使われ方：辺の始点への制限の共通自明 span。 -/
lemma rightFibrationMappingDiagramRestriction_trivialKanFibration
    {K L E B : SSet.{u}} [Quasicategory E] (r : E ⟶ B) (p : K ⟶ E)
    (i : L ⟶ K) [Mono i] (hi : leftAnodyneExtensions i) {q : L ⟶ E}
    (hq : i ≫ p = q) (x : B _⦋0⦌) :
    TrivialKanFibration (rightFibrationMappingDiagramRestriction r p i hq x) := by
  have ht := sliceOverRestrict_trivialKanFibration p i hi
  letI : TrivialKanFibration (normalizedConeRestriction p i hq) := ⟨by
    exact trivialKanFibrations.comp_mem _ _ ht.mem (MorphismProperty.rlp_of_isIso _ _)⟩
  exact vertexFiberMap_trivialKanFibration _ _ _ _ x

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
