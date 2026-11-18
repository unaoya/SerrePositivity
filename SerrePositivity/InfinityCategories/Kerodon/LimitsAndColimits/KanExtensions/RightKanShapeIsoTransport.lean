module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightExistence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCoslicePostIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitDiagramIso

/-!
概要：始域・終域の指定同型で揃えた右 Kan の局所図式を同じ係数とともに移送する。
方針：既存の point coslice の同型と引き戻しの同型を合成し、射影を保持する。
規約：元の右 Kan の写像と指定した底の同型の可換四角形を保持する。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の元の反対 Yoneda への形状移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {K K' C C' D : SSet.{u}} (a : K ≅ K') (b : C ≅ C')
  {δ : K ⟶ C} {δ' : K' ⟶ C'} (hw : δ ≫ b.hom = a.hom ≫ δ')

/-- 同じ可換な同型の四角形は、対応する点の右 Kan 局所形状の指定同型を与える。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の coslice と引き戻しの同型の移送則。 -/
def rightKanShapeIsoOfSquare (c : C _⦋0⦌) :
    rightKanShape δ c ≅ rightKanShape δ' (b.hom.app (Opposite.op ⦋0⦌) c) :=
  asIso (pullback.map (sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ
    (sliceUnderProjection (SSet.yonedaEquiv.symm (b.hom.app (Opposite.op ⦋0⦌) c))) δ'
    (pointCoslicePostIso b c).hom a.hom b.hom (pointCoslicePostIso_projection b c).symm hw)

/-- 局所形状の同じ指定同型は、元の始域の同型に沿って射影を保持する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、同じ係数を引き戻すための射影の法則。 -/
lemma rightKanShapeIsoOfSquare_projection (c : C _⦋0⦌) :
    (rightKanShapeIsoOfSquare a b hw c).hom ≫
      rightKanProjection δ' (b.hom.app (Opposite.op ⦋0⦌) c) = rightKanProjection δ c ≫ a.hom :=
  pullback.lift_snd _ _ _

include hw in
/-- 同じ可換な同型の四角形で、元の係数を持つ右 Kan 局所図式の極限の存在を移す。
Kerodon Definition 7.3.1.2（Tag 02Y9）、局所形状の指定同型に沿う係数移送則。 -/
lemma hasLimit_rightKanDiagram_iff_of_isoSquare [Quasicategory D]
    (O : K' ⟶ D) (c : C _⦋0⦌) :
    HasLimit (rightKanDiagram δ (a.hom ≫ O) c) ↔
      HasLimit (rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) c)) := by
  have hh := hasLimit_iff_restrict_of_precompositionEquivalence
    (rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) c))
    (rightKanShapeIsoOfSquare a b hw c).hom
    (isPrecompositionEquivalence_of_iso (rightKanShapeIsoOfSquare a b hw c))
  simpa only [rightKanDiagram, ← Category.assoc, rightKanShapeIsoOfSquare_projection] using hh.symm

include hw in
/-- 同じ始域・終域の指定同型で、全変換を持つ右 Kan 延長の存在を移す。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の局所存在判定と形状移送の合成則。 -/
lemma exists_rightKanExtension_iff_of_isoSquare
    [Quasicategory K] [Quasicategory K'] [Quasicategory C] [Quasicategory C'] [Quasicategory D]
    (O : K' ⟶ D) :
    (∃ (G : C ⟶ D) (ε : SSet.Homotopy (δ ≫ G) (a.hom ≫ O)),
      IsRightKanExtension δ (a.hom ≫ O) G ε) ↔
    (∃ (G : C' ⟶ D) (ε : SSet.Homotopy (δ' ≫ G) O), IsRightKanExtension δ' O G ε) := by
  rw [exists_kanRightExtension_iff_local_limits, exists_kanRightExtension_iff_local_limits]
  constructor
  · intro h c'
    obtain ⟨c, rfl⟩ := (isIso_iff_bijective (b.hom.app (Opposite.op ⦋0⦌))).mp inferInstance |>.2 c'
    exact (hasLimit_rightKanDiagram_iff_of_isoSquare a b hw O c).mp (h c)
  · intro h c
    exact (hasLimit_rightKanDiagram_iff_of_isoSquare a b hw O c).mpr (h _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
