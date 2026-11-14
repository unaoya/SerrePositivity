module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFixedComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatJoinRightTensor

/-! # 太い coslice の余錐

概要：左図式を固定する fat join 上の関手を太い coslice の族として表示する。
方針：太い零単体の余錐の制限射の fiber を使う。
規約：既存の coslice・coconeFamily を変更しない。使われ方：余錐の族の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：太い零単体の余錐を左図式上で固定した太い coslice。
方針：左包含による前合成の fiber を取る。
規約：図式を高次単体でも固定する。使われ方：coslice 比較の中間模型。 -/
def laxCoslice {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}))).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：太い coslice は値域が quasicategory なら quasicategory。
方針：左包含の単射による前合成の inner fibration の fiber を取る。
規約：図式の形状は任意。使われ方：比較同値の圏構造。 -/
instance laxCoslice_quasicategory {K X : SSet.{u}} [Quasicategory X] (p : K ⟶ X) :
    Quasicategory (laxCoslice p) := by
  unfold laxCoslice
  infer_instance

/-- 概要：通常の余錐の関手圏から太い coslice への比較射。
方針：fat join 比較の前合成を固定図式の fiber に制限する。
規約：左図式は p。使われ方：coslice の二つの模型の比較。 -/
def coconeFamilyLaxCosliceMap {K X : SSet.{u}} (p : K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily p ⟶ laxCoslice p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedDiagramPre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_comparison K Δ[0]) p

/-- 概要：余錐の関手圏と太い coslice の比較は同値。
方針：左図式を固定した fat join 比較を使う。
規約：値域は quasicategory。使われ方：coslice 比較の二対三則。 -/
lemma isQCatEquivalence_coconeFamilyLaxCosliceMap {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (coconeFamilyLaxCosliceMap p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isQCatEquivalence_fatJoinComparison_fixedLeftDiagram K Δ[0] X p

/-- 概要：太い余錐の関手からパラメーター付きの太い零単体の余錐の族を作る。
方針：パラメーターを fat join の右因子へ移して零単体を忘れる。
規約：余錐の形を直積の第一因子とする。使われ方：太い coslice の curry。 -/
def laxCosliceCurryFamily {A K X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K (Δ[0] : SSet.{u}) ⊗ A ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight K Δ[0] A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap (𝟙 K) (snd Δ[0] A) ≫ F

/-- 概要：太い余錐の族は左図式上で固定される。
方針：右直積比較と fat join の左包含の式を使う。
規約：全てのパラメーターで図式を固定する。使われ方：fiber への持ち上げ。 -/
lemma laxCosliceCurryFamily_fixed {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ F = p) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}) ▷ A) ≫ laxCosliceCurryFamily F = fst K A ≫ p := by
  rw [laxCosliceCurryFamily,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K (Δ[0] : SSet.{u}) ▷ A), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableFatJoinTensorRight_inl]
  simp only [Category.assoc, reassoc_of% _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map, Category.id_comp, hF]

/-- 概要：左図式を固定する太い余錐の関手を太い coslice へ curry する。
方針：普遍族の curry を固定図式上の fiber に持ち上げる。
規約：パラメーターの quasicategory 性は不要。使われ方：太い coslice の普遍性。 -/
def laxCosliceCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K A ≫ F = p) : A ⟶ laxCoslice p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (curry (laxCosliceCurryFamily F)) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, laxCosliceCurryFamily_fixed F hF]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨k, a⟩
    dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex]
    rfl)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
