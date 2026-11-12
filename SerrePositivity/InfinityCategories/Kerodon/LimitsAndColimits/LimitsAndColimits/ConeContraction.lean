module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeCollapse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePrisms

/-!
概要：錐を頂点へ縮める円柱と、底・頂点・時間両端の厳密な計算。
方針：底の各点を右の点付き円柱へ動かし、二つの頂点を一つに潰す。
規約：時間を第一因子とする。
使われ方：comma 内の比較を相対 join の局所余錐の比較へ持ち上げる底の円柱。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：底の円柱に点を付加したものを元の錐へ写す。
方針：底を右の点付き円柱で動かして二つの頂点を潰す。
規約：底側は Δ¹×A。
使われ方：変動する底の錐の族の構成。 -/
def coneContractionCore (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[1] : SSet.{u}) ⊗ A) Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A) (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneCollapse A

/-- 概要：錐の底側の円柱は標準の右の点付き円柱になる。
方針：join の左包含と頂点を潰す射の左境界。
規約：時間を保つ。
使われ方：comma 内の比較の底への射影との照合。 -/
lemma coneContractionCore_inl (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((Δ[1] : SSet.{u}) ⊗ A) Δ[0] ≫ coneContractionCore A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A := by
  rw [coneContractionCore, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneCollapse_left, Category.comp_id]

/-- 概要：付加した頂点は元の錐の頂点に固定される。
方針：join の右包含と頂点を潰す射の右境界。
規約：標準零単体の射として一致する。
使われ方：頂点固定の余錐の比較。 -/
lemma coneContractionCore_inr (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((Δ[1] : SSet.{u}) ⊗ A) Δ[0] ≫ coneContractionCore A = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  rw [coneContractionCore, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneCollapse_right]

/-- 概要：底の円柱の時間零への制限は元の錐を回収する。
方針：右の円柱の零端点と三因子の中間包含。
規約：両端の頂点を同じものとして潰す。
使われ方：比較の始端の底の係数。 -/
lemma coneContractionCore_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A) (𝟙 (Δ[0] : SSet.{u})) ≫ coneContractionCore A = 𝟙 _ := by
  rw [coneContractionCore, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneCollapse_middle]

/-- 概要：底の円柱の時間一への制限は錐の頂点に定値になる。
方針：右の円柱の一端点を二つの点の包含に分解して潰す。
規約：底のパラメータ全体を標準零単体へ写す。
使われ方：比較の終端の底の係数。 -/
lemma coneContractionCore_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) (𝟙 (Δ[0] : SSet.{u})) ≫ coneContractionCore A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  rw [coneContractionCore, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_one]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (SSet.const (stdSimplex.obj₀Equiv.symm 0) : A ⟶ Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u}))
  simp only [Category.id_comp] at h
  rw [h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneCollapse_rightPair, ← Category.assoc]
  congr 1

/-- 概要：錐の恒等射からその頂点の定値射への円柱。
方針：時間と join の比較の後に底の円柱を使う。
規約：頂点は全時刻で固定される。
使われ方：相対 join に持ち上げる底のホモトピー。 -/
def coneContraction (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft Δ[1] A Δ[0] ≫ coneContractionCore A

/-- 概要：錐の収縮の時間零は恒等射。
方針：直積比較の零端点と底の円柱の零端点。
規約：元の錐全体を回収する。
使われ方：局所余錐の比較の始端。 -/
lemma coneContraction_zero (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ≫ coneContraction A = 𝟙 _ := by
  rw [coneContraction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_joinTensorLeft_prismEndpoint,
    coneContractionCore_zero]

/-- 概要：錐の収縮の時間一は頂点の定値射。
方針：直積比較の一端点と底の円柱の一端点。
規約：底を潰す。
使われ方：局所余錐の比較の終端。 -/
lemma coneContraction_one (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ≫ coneContraction A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] := by
  rw [coneContraction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_joinTensorLeft_prismEndpoint,
    coneContractionCore_one]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
