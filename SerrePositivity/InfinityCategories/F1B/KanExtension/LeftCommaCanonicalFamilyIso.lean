module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftTransportTargetEq
public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeFamilyPrismIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalCriterion

/-!
概要：標準余錐と普遍 comma 余錐の制限を図式固定の余錐の族の中で比較する。
方針：普遍自己変換の恒等性と図式固定の比較円柱の同型を合成する。
規約：余錐全体の関手同型に加え、元の局所図式を固定した同型を得る。
使われ方：標準底余錐上の相対余極限の存在を普遍底余錐へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：普遍 comma 余錐の制限は元の標準局所図式の余錐として読める。
方針：左端の等式と局所添字の射影の一致を計算する。
規約：余錐の raw な射は制限した普遍 comma 余錐そのもの。
使われ方：底余錐の同型の両端の型を同じ固定図式に揃える。 -/
def kanLeftCommaUniversalLocalCocone {K C D : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    JoinCocone (leftKanDiagram δ (δ ≫ F) c) := by
  let H := kanLeftCommaUniversalDiagram δ ≫ F
  let b := kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H
  let i := kanLeftKanShapeToCommaFiber δ c
  refine ⟨(b.restrict i).val, (b.restrict i).property.trans ?_⟩
  have h := congrArg (fun q ↦ i ≫ vertexFiberι (kanLeftCommaProjection δ) c ≫ q)
    (kanLeftCommaUniversalFamily_diagram δ F)
  have hs := congrArg (fun q ↦ q ≫ (δ ≫ F)) (kanLeftKanShapeToCommaFiber_source δ c)
  exact h.trans (by simpa only [i, Category.assoc, leftKanDiagram] using hs)

/-- 概要：普遍 comma 余錐の制限と標準余錐は図式固定の余錐の族の中で同型。
方針：候補の単位の類を恒等へ戻し、局所輸送の同型と比較円柱の同型を合成する。
規約：同型は標準の局所図式を全時間固定する。
使われ方：局所相対余極限を底余錐の表示によらず移す。 -/
def kanLeftCommaCanonicalFamilyIso {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    VertexIso (coconeFamilyVertexEquiv _ (leftKanCanonicalCocone δ F c))
      (coconeFamilyVertexEquiv _ (kanLeftCommaUniversalLocalCocone δ F c)) := by
  let H := kanLeftCommaUniversalDiagram δ ≫ F
  let hH := kanLeftCommaUniversalFamily_diagram δ F
  let t := kanLeftCommaCoconeTransport δ (δ ≫ F) H hH c
  let α := functorHomotopyPostcomp (kanLeftCommaUniversalIdentityHomotopy δ) F
  let t' := kanLeftTransportTargetEq (kanLeftCommaUniversalFamily_candidate δ F)
    (β := α) (show (kanLeftCommaCandidateTransformation δ (δ ≫ F) H hH).h = α.h from rfl) t
  let s := kanRelativeLeftReflTransport δ F c
  let eo := Classical.choice (t'.coconeFamily_opIso_of_homMk_eq
    (kanLeftCommaUniversalIdentityHomotopy_postcomp_hom δ F) s)
  have et := kanVertexIso_unop eo
  have ht : t'.cocone = t.cocone := kanLeftTransportTargetEq_cocone _ _ t
  have hs : s.cocone = leftKanCanonicalCocone δ F c := Subtype.ext rfl
  rw [ht, hs] at et
  let P := kanLocalRelativeJoinConeComparison δ c ≫ H
  have hd : (Δ[1] ◁ joinInl (leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ P =
      snd Δ[1] (leftKanShape δ c) ≫ leftKanDiagram δ (δ ≫ F) c := by
    rw [← Category.assoc]
    exact kanLocalRelativeJoinConeComparison_diagram δ (δ ≫ F) H hH c
  have hv : (Δ[1] ◁ joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})) ≫ P =
      snd Δ[1] (Δ[0] : SSet.{u}) ≫ (SSet.yonedaEquiv.symm c ≫ kanLeftCommaCandidate δ H) := by
    rw [← Category.assoc]
    exact kanLocalRelativeJoinConeComparison_vertex δ H c
  have ep := SerrePositivity.InfinityCategories.F1B.coconeFamilyPrismIso t.cocone (kanLeftCommaUniversalLocalCocone δ F c) P hd
    (kanLocalRelativeJoinConeComparison_zero δ (δ ≫ F) H hH c)
    (kanLocalRelativeJoinConeComparison_one δ H c) (fun x ↦ by
      obtain ⟨a, rfl⟩ | ⟨b, rfl⟩ := SerrePositivity.InfinityCategories.F1B.join_vertex_cases (leftKanShape δ c) Δ[0] x
      · exact SerrePositivity.InfinityCategories.F1B.prism_vertical_invertible_of_fixed_map P _ _ hd a
      · exact SerrePositivity.InfinityCategories.F1B.prism_vertical_invertible_of_fixed_map P _ _ hv b)
  exact et.symm ≪≫ ep

end SerrePositivity.InfinityCategories.F1B
