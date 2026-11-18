module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex

/-!
概要：指定した形状同型の可換四角形で、右 Kan 局所図式の指定極限の頂点を比較する。
方針：検証済みの局所形状同型の射影の等式で係数を揃え、極限の一意性を使う。
規約：始域・終域の同型と元の指定極限錐を引数に保つ。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、HTT 5.1.5.6、S8。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

local instance rightKanShapeIsoLimitVertex_projection {K C : SSet.{u}}
    [Quasicategory C] (δ : K ⟶ C) (v : C _⦋0⦌) :
    LeftFibration (rightKanProjection δ v) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm v)))⟩

local instance rightKanShapeIsoLimitVertex_quasicategory {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) (v : C _⦋0⦌) :
    Quasicategory (rightKanShape δ v) := quasicategory_of_innerFibration (rightKanProjection δ v)

/-- 同じ可換な形状同型の四角形で、元の係数を持つ指定局所極限の頂点を比較する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、指定形状同型の射影と極限の一意性の移送則。 -/
def rightKanLimitVertexIsoOfIsoSquare {K K' C C' D : SSet.{u}}
    [Quasicategory K] [Quasicategory K'] [Quasicategory C] [Quasicategory C'] [Quasicategory D]
    (a : K ≅ K') (b : C ≅ C') {δ : K ⟶ C} {δ' : K' ⟶ C'}
    (hw : δ ≫ b.hom = a.hom ≫ δ') (O : K' ⟶ D) (v : C _⦋0⦌)
    (c : JoinCone (rightKanDiagram δ (a.hom ≫ O) v))
    (d : JoinCone (rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v)))
    (hc : IsLimitCone c) (hd : IsLimitCone d) : VertexIso c.vertex d.vertex := by
  let s := rightKanShapeIsoOfSquare a b hw v
  let t := restrictJoinCone d s.hom
  have ht := (SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape
    s.hom (isPrecompositionEquivalence_of_iso s).isQCatEquivalence d).mp hd
  have he : rightKanDiagram δ (a.hom ≫ O) v =
      s.hom ≫ rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v) := by
    rw [rightKanDiagram, rightKanDiagram, ← Category.assoc]
    change _ = (rightKanShapeIsoOfSquare a b hw v).hom ≫ _ ≫ O
    rw [← Category.assoc, rightKanShapeIsoOfSquare_projection, Category.assoc]
  have e := limitVertexIsoOfDiagramEq he c t hc ht
  exact (restrictJoinCone_vertex d s.hom) ▸ e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
