module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftTransportTargetEq
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamilyPrismIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaUniversalCriterion

/-!
概要：標準余錐と普遍 comma 余錐の制限を図式固定の余錐の族の中で比較する。
方針：普遍自己変換の恒等性と図式固定の比較円柱の同型を合成する。
規約：余錐全体の関手同型に加え、元の局所図式を固定した同型を得る。
使われ方：標準底余錐上の相対余極限の存在を普遍底余錐へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：普遍 comma 余錐の制限は元の標準局所図式の余錐として読める。
方針：左端の等式と局所添字の射影の一致を計算する。
規約：余錐の raw な射は制限した普遍 comma 余錐そのもの。
使われ方：底余錐の同型の両端の型を同じ固定図式に揃える。 -/
def kanLeftCommaUniversalLocalCocone {K C D : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ (δ ≫ F) c) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c H
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiber δ c
  refine ⟨(b.restrict i).val, (b.restrict i).property.trans ?_⟩
  have h := congrArg (fun q ↦ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_diagram δ F)
  have hs := congrArg (fun q ↦ q ≫ (δ ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiber_source δ c)
  exact h.trans (by simpa only [i, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram] using hs)

/-- 概要：普遍 comma 余錐の制限と標準余錐は図式固定の余錐の族の中で同型。
方針：候補の単位の類を恒等へ戻し、局所輸送の同型と比較円柱の同型を合成する。
規約：同型は標準の局所図式を全時間固定する。
使われ方：局所相対余極限を底余錐の表示によらず移す。 -/
def kanLeftCommaCanonicalFamilyIso {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv _ (kanLeftCommaUniversalLocalCocone δ F c)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalDiagram δ ≫ F
  let hH := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_diagram δ F
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCoconeTransport δ (δ ≫ F) H hH c
  let α := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalIdentityHomotopy δ) F
  let t' := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransportTargetEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalFamily_candidate δ F)
    (β := α) (show (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidateTransformation δ (δ ≫ F) H hH).h = α.h from rfl) t
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftReflTransport δ F c
  let eo := Classical.choice (t'.coconeFamily_opIso_of_homMk_eq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaUniversalIdentityHomotopy_postcomp_hom δ F) s)
  have et := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanVertexIso_unop eo
  have ht : t'.cocone = t.cocone := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftTransportTargetEq_cocone _ _ t
  have hs : s.cocone = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c := Subtype.ext rfl
  rw [ht, hs] at et
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalRelativeJoinConeComparison δ c ≫ H
  have hd : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ P =
      snd Δ[1] (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ (δ ≫ F) c := by
    rw [← Category.assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalRelativeJoinConeComparison_diagram δ (δ ≫ F) H hH c
  have hv : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ P =
      snd Δ[1] (Δ[0] : SSet.{u}) ≫ (SSet.yonedaEquiv.symm c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaCandidate δ H) := by
    rw [← Category.assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalRelativeJoinConeComparison_vertex δ H c
  have ep := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyPrismIso t.cocone (kanLeftCommaUniversalLocalCocone δ F c) P hd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalRelativeJoinConeComparison_zero δ (δ ≫ F) H hH c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalRelativeJoinConeComparison_one δ H c) (fun x ↦ by
      obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join_vertex_cases (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c) Δ[0] x
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prism_vertical_invertible_of_fixed_map P _ _ hd a
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prism_vertical_invertible_of_fixed_map P _ _ hv b)
  exact et.symm ≪≫ ep

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
