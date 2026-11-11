module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeUnitCylinder
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitUnitFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily

/-!
概要：元の全単位族の両端を、元の図式と頂点への定値図式に厳密に同定する。
方針：元の join 円柱の両端を使い、全パラメータで前合成の式を計算する。
規約：頂点だけでなく射の等式。使われ方：単位三角柱の上下の全二単体。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全単位族の時刻評価は、同じ時刻の join 円柱による前合成そのもの。 -/
lemma coconeUnitFamily_evaluate {K X T : SSet.{u}}
    (q : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X) (t : (Δ[1] : SSet.{u}) _⦋0⦌) :
    lift (𝟙 T) (SSet.const t) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeUnitFamily q =
      q ≫ (pre (lift (𝟙 K) (SSet.const t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K)).app X := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- 元の単位 join 円柱の始端は元の左包含。 -/
lemma coconeUnitCylinderMap_zero (K : SSet.{u}) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) := by
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h, c, Category.comp_id] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c).h₀

/-- 元の単位 join 円柱の終端は元の右頂点への定値写像。 -/
lemma coconeUnitCylinderMap_one (K : SSet.{u}) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K =
      SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))) := by
  let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h, c, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c).h₁

/-- 元の全余錐族の単位は、時間零で元の図式への制限に厳密に一致。 -/
lemma coconeUnitFamily_zero {K X T : SSet.{u}}
    (q : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X) :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeUnitFamily q = q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X := by
  change lift (𝟙 T) (SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeUnitFamily q = _
  rw [coconeUnitFamily_evaluate]
  change q ≫ (pre (SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K)).app X = _
  rw [coconeUnitCylinderMap_zero]
  rfl

/-- 元の全余錐族の単位は、時間一で元の右頂点への前合成に厳密に一致。 -/
lemma coconeUnitFamily_one {K X T : SSet.{u}}
    (q : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X) :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeUnitFamily q =
      q ≫ (pre (SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))))).app X := by
  change lift (𝟙 T) (SSet.const (stdSimplex.obj₀Equiv.symm 1)) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coconeUnitFamily q = _
  rw [coconeUnitFamily_evaluate]
  change q ≫ (pre (SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K)).app X = _
  rw [coconeUnitCylinderMap_one]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
