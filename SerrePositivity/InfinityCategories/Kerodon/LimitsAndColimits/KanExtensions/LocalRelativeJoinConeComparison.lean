module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LocalCommaIdentityComparison

/-!
概要：comma 内の局所比較を相対 join 内の余錐の比較へ持ち上げる。
方針：slice の標準余錐を頂点へ縮める係数と、comma の局所比較の底への射影を照合する。
規約：図式と頂点は後合成後に全時間で固定する。
使われ方：標準局所輸送の余錐と comma fiber の余錐の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：comma の局所比較の底への射影は slice の円柱展開と一致する。
方針：局所比較の射影の公式と標準変換の第一因子を時間とする展開。
規約：raw な円柱の射を比較する。
使われ方：局所比較を相対 join の余錐比較へ持ち上げる係数条件。 -/
lemma kanLocalRelativeJoinConeComparison_condition {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    (β_ (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalCommaIdentityComparison δ c).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalCommaIdentityComparison_projection]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy_prism c _

/-- 概要：標準の局所余錐から comma fiber の底へ動かした余錐への相対 join 内の比較。
方針：comma の局所比較と slice の係数で一般の相対 join の錐の比較を適用する。
規約：時間を第一因子に置く。
使われ方：局所輸送の余錐の普遍性を fiber の普遍性から得る。 -/
def kanLocalRelativeJoinConeComparison {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalCommaIdentityComparison δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))))
    (SSet.yonedaEquiv.symm c) (kanLocalRelativeJoinConeComparison_condition δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed _)

/-- 概要：局所比較の始端に図式を後合成すると標準局所輸送の余錐になる。
方針：相対 join の錐の比較の零境界と輸送の始端の式を使う。
規約：左端の元の図式は hH で保つ。
使われ方：比較の始端を点ごとの Kan 条件の余錐と同定する。 -/
lemma kanLocalRelativeJoinConeComparison_zero {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫
      kanLocalRelativeJoinConeComparison δ c ≫ H =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCoconeTransport δ F₀ H hH c).cocone.val := by
  rw [← Category.assoc]
  unfold kanLocalRelativeJoinConeComparison
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinConeComparison_zero _ _ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLocalBase_condition δ c)]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCoconeTransport_cocone_val δ F₀ H hH c).symm

/-- 概要：後合成した局所比較は底の図式を全時間で固定する。
方針：左境界を元の図式へ制限し、comma の局所比較の元の添字の固定式を使う。
規約：F₀ の制限上の定値な族。
使われ方：同じ図式上の余錐のホモトピーとして比較する。 -/
lemma kanLocalRelativeJoinConeComparison_diagram {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)
    (c : C _⦋0⦌) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0]) ≫
      kanLocalRelativeJoinConeComparison δ c ≫ H =
        snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c := by
  rw [← Category.assoc]
  unfold kanLocalRelativeJoinConeComparison
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinConeComparison_inl, Category.assoc, Category.assoc, hH,
    ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalCommaIdentityComparison δ c).h,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalCommaIdentityComparison_source]
  rfl

/-- 概要：後合成した局所比較は余錐の頂点を全時間で固定する。
方針：相対 join の比較の右境界を使う。
規約：頂点は候補図式の c での値。
使われ方：固定頂点上の余錐間の比較。 -/
lemma kanLocalRelativeJoinConeComparison_vertex {K C D : SSet.{u}} (δ : K ⟶ C)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0]) ≫
      kanLocalRelativeJoinConeComparison δ c ≫ H =
        snd (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H := by
  rw [← Category.assoc]
  unfold kanLocalRelativeJoinConeComparison
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinConeComparison_inr]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
