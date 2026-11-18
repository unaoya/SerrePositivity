module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoCanonical
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：形状同型の可換四角形に沿って、同じ全関手と指定変換の右 Kan 条件を移す。
方針：既存の局所形状同型で輸送の円柱全体を制限し、同じ終端の極限性を移す。
規約：全関手と指定変換を結論に保持し、局所極限の存在だけに置き換えない。
使われ方：Kerodon Definition 7.3.1.2（Tag 02Y9）、HTT 5.1.5.6 の形状移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {K K' C C' D : SSet.{u}} (a : K ≅ K') (b : C ≅ C')
  {δ : K ⟶ C} {δ' : K' ⟶ C'} (hw : δ ≫ b.hom = a.hom ≫ δ')
  {O : K' ⟶ D} {F : C' ⟶ D} (α : SSet.Homotopy (δ' ≫ F) O)

/-- 同じ形状同型の四角形で、元の指定余単位の全円柱を制限する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の前合成と端点の等式の移送則。 -/
def rightKanCounitIsoSquare : SSet.Homotopy (δ ≫ (b.hom ≫ F)) (a.hom ≫ O) where
  h := (functorHomotopyPrecomp α a.hom).h
  h₀ := (functorHomotopyPrecomp α a.hom).h₀.trans (by
    rw [← Category.assoc, ← hw, Category.assoc]
    rfl)
  h₁ := (functorHomotopyPrecomp α a.hom).h₁
  rel := (functorHomotopyPrecomp α a.hom).rel

/-- 同じ局所形状同型で、指定輸送の円柱全体を前合成する。
Kerodon Definition 7.3.1.2（Tag 02Y9）、元の標準錐・図式・頂点を保持する移送則。 -/
def rightKanTransportIsoSquare (v : C _⦋0⦌)
    (t : RightKanConeTransport δ' O F α (b.hom.app (Opposite.op ⦋0⦌) v)) :
    RightKanConeTransport δ (a.hom ≫ O) (b.hom ≫ F) (rightKanCounitIsoSquare a b hw α) v where
  family := (joinMap (𝟙 (Δ[0] : SSet.{u})) (rightKanShapeIsoOfSquare a b hw v).hom ▷ Δ[1]) ≫ t.family
  start := by
    rw [SSet.ι₀_comp_assoc, t.start]
    exact rightKanShapeIsoOfSquare_canonical_val a b hw F v
  diagram := by
    rw [← Category.assoc, ← comp_whiskerRight, joinInr_joinMap, comp_whiskerRight,
      Category.assoc, t.diagram, ← Category.assoc, ← comp_whiskerRight,
      rightKanShapeIsoOfSquare_projection, comp_whiskerRight, Category.assoc]
    rfl
  fixedVertex := by
    rw [← Category.assoc, ← comp_whiskerRight, joinInl_joinMap, Category.id_comp, t.fixedVertex]
    have he := congrArg (fun f => joinInl (Δ[0] : SSet.{u}) (rightKanShape δ v) ≫ f)
      (rightKanShapeIsoOfSquare_canonical_val a b hw F v)
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at he
    exact congrArg (fun f => fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ f) he

/-- 移送した同じ円柱の終端は、元の指定錐の局所形状同型による制限そのもの。
Kerodon Definition 7.3.1.2（Tag 02Y9）、円柱の終端と前合成の法則。 -/
lemma rightKanTransportIsoSquare_cone_val (v : C _⦋0⦌)
    (t : RightKanConeTransport δ' O F α (b.hom.app (Opposite.op ⦋0⦌) v)) :
    (rightKanTransportIsoSquare a b hw α v t).cone.val =
      (restrictJoinCone t.cone (rightKanShapeIsoOfSquare a b hw v).hom).val := by
  change SSet.ι₁ ≫ (_ ≫ t.family) = _ ≫ (SSet.ι₁ ≫ t.family)
  rw [SSet.ι₁_comp_assoc]

local instance rightKanShapeIsoData_projection {A B : SSet.{u}} [Quasicategory B]
    (f : A ⟶ B) (v : B _⦋0⦌) : LeftFibration (rightKanProjection f v) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := sliceUnderProjection _))⟩
local instance rightKanShapeIsoData_quasicategory {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (f : A ⟶ B) (v : B _⦋0⦌) : Quasicategory (rightKanShape f v) :=
  quasicategory_of_innerFibration (rightKanProjection f v)

/-- 形状同型の可換四角形は、元の全関手と同じ指定余単位の右 Kan 条件を移す。
Kerodon Definition 7.3.1.2（Tag 02Y9）、指定円柱と同値な添字での極限の移送則。 -/
lemma kanRightKanExtension_of_isoSquare
    [Quasicategory K] [Quasicategory K'] [Quasicategory C] [Quasicategory C'] [Quasicategory D]
    (hα : IsRightKanExtension δ' O F α) :
    IsRightKanExtension δ (a.hom ≫ O) (b.hom ≫ F) (rightKanCounitIsoSquare a b hw α) := by
  intro v
  obtain ⟨t, ht⟩ := hα (b.hom.app (Opposite.op ⦋0⦌) v)
  refine ⟨rightKanTransportIsoSquare a b hw α v t, ?_⟩
  have hr := (isLimitCone_iff_restrict_equivalentShape
    (rightKanShapeIsoOfSquare a b hw v).hom
    (isPrecompositionEquivalence_of_iso (rightKanShapeIsoOfSquare a b hw v)).isQCatEquivalence
    t.cone).mp ht
  exact (isLimitCone_iff_of_cone_val_eq _ _
    (rightKanTransportIsoSquare_cone_val a b hw α v t)).mpr hr

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
