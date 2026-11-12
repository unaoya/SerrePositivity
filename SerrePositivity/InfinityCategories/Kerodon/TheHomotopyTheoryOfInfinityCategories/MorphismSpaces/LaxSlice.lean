module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFixedDiagramComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：太い join による錐の関手単体集合の模型。
方針：太い零単体の join からの関手を右図式の頂点上の fiber に制限する。
規約：既存の slice や coneFamily は変更しない。
使われ方：Kerodon §4.6.4（Tag 01KE）・4.6.6（Tag 04HY） の太い slice の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：太い零単体の join からの関手を右図式上で固定した太い slice。
方針：右包含の前合成の fiber を取る。
規約：図式 p を高次単体でも厳密に固定する。
使われ方：Kerodon §4.6.4（Tag 01KE）・4.6.6（Tag 04HY） の比較の中間模型。 -/
@[kerodon 01KU]
noncomputable def laxSlice {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K)).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：太い slice は値域が quasicategory なら quasicategory。
方針：右包含の単射による前合成の inner fibration の fiber を使う。
規約：添字 K は任意。
使われ方：Kerodon §4.6.4（Tag 01KE） の太い slice の圏構造。 -/
instance laxSlice_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (laxSlice p) := by
  unfold laxSlice
  infer_instance

/-- 概要：通常の錐の関手単体集合の模型から太い slice への比較。
方針：太い join の比較の前合成を図式の fiber へ制限する。
規約：右図式は p。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の比較の中間射。 -/
noncomputable def coneFamilyLaxSliceMap {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily p ⟶ laxSlice p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)).app X)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K)).app X)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison (Δ[0] : SSet.{u}) K)).app X)
    (by rw [← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_comparison]) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：通常の錐の関手単体集合の模型と太い slice の比較は同値。
方針：固定図式上の fat join 比較を零単体の左因子に適用する。
規約：X は quasicategory、K は任意。
使われ方：Kerodon Example 4.6.6.8（Tag 04J5） の中間模型の同値。 -/
lemma isQCatEquivalence_coneFamilyLaxSliceMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coneFamilyLaxSliceMap p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_fatJoinComparison_fixedDiagram Δ[0] K X p

/-- 概要：太い join 上の関手からパラメーター付きの太い零単体の錐の族を作る。
方針：直積の比較でパラメーターを左因子へ移して零単体の成分を忘れる。
規約：錐の形を直積の第一因子とする。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice の curry の準備。 -/
noncomputable def laxSliceCurryFamily {A K X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K ⊗ A ⟶ X :=
  (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K) A).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorLeft A Δ[0] K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (fst A Δ[0]) (𝟙 K) ≫ F

/-- 概要：太い join の関手が右図式を固定すると対応する族も右図式を固定する。
方針：直積の比較と太い join の射の右包含上の計算を使う。
規約：全てのパラメーターで図式を固定する。
使われ方：Kerodon §4.6.6（Tag 04HY） の fiber への持ち上げの条件。 -/
lemma laxSliceCurryFamily_fixed {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ≫ laxSliceCurryFamily F = fst K A ≫ p := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A) ≫
      (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) K) A).hom =
        (β_ K A).hom ≫ (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K) := rfl
  rw [laxSliceCurryFamily, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr (Δ[0] : SSet.{u}) K ▷ A), hs]
  simp only [Category.assoc]
  rw [← Category.assoc (A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] K), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinTensorLeft_inr]
  simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map, Category.id_comp, hF]
  rfl

/-- 概要：右図式を固定する太い join 上の関手を太い slice への射へ curry する。
方針：普遍族の curry を図式の fiber に持ち上げる。
規約：A、K、X の quasicategory 性は不要。
使われ方：Kerodon §4.6.6（Tag 04HY） の太い slice の普遍性。 -/
noncomputable def laxSliceCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A K ≫ F = p) : A ⟶ laxSlice p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry (laxSliceCurryFamily F)) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, laxSliceCurryFamily_fixed F hF]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨k, a⟩
    dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex]
    rfl)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
