module

public import SerrePositivity.InfinityCategories.F2.Presentable.RelativeJoinColimitPreservation
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullyFaithfulPrecompositionColimits
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：局所左 Kan 図式と延長先図式の余極限保存を元の図式へ戻す。
方針：comma fiber と元の局所図式の比較を全余錐の同型で後合成する。
規約：指定された元の余錐像を扱う。
使われ方：小余積と幾何学的実現からの全小余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：局所図式を保存すれば相対 join の同じ fiber 余極限を保存する。
方針：元の局所輸送余錐に保存を使い、全余錐同型と前合成同値で戻す。
規約：図式比較の自然性を全余錐で保持する。
使われ方：全小余極限保存の局所判定。 -/
lemma relativeJoinFiber_isColimit_postcomp_of_local
    {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] (δ : A ⟶ B) (F : A ⟶ X) (U : X ⟶ Y)
    (H : relativeJoin (F1B.kanLeftCommaProjection δ) (𝟙 B) ⟶ X)
    (hH : relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B) ≫ H =
      F1B.kanLeftCommaSource δ ≫ F)
    (b : B.obj (Opposite.op ⦋0⦌))
    (hc : IsColimitCone
      (F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b H))
    (hU : ∀ c : JoinCocone (leftKanDiagram δ F b),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c)) :
    IsColimitCone
      (F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b (H ≫ U)) := by
  have ht := hU (F1B.kanLeftCommaCoconeTransport δ F H hH b).cocone
    (F1B.kanLeftCommaCoconeTransport_isColimit δ F H hH b hc)
  have he := (F1B.kanLeftCommaCoconeTransport_functorIso δ F H hH b).postcomp U
  let c := F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b (H ≫ U)
  have ha := (F1B.kanLeftKanShapeToCommaFiber_isPrecompositionEquivalence δ b) Y
  apply (isColimitCone_iff_restrict_of_fullyFaithful_pre
    (F1B.kanLeftKanShapeToCommaFiber δ b)
    ha.choose.isFullyFaithful c).mpr
  exact F1B.kanIsColimitCone_of_functorIso ht he

/-- 概要：局所左 Kan 余極限と延長先余極限の保存から元の余極限保存を得る。
方針：局所余極限で構成した相対 join の図式の両端を比較する。
規約：元の指定余錐を結論に残す。
使われ方：bar 図式を使う一般保存判定の合成段階。 -/
lemma colimitPreservation_of_localLeftKan
    {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] (δ : A ⟶ B) (F : A ⟶ X) (U : X ⟶ Y)
    (hlocal : ∀ b, HasColimit (leftKanDiagram δ F b))
    (hU : ∀ b (c : JoinCocone (leftKanDiagram δ F b)),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c))
    (hB : ∀ (G : B ⟶ X) (c : JoinCocone G),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c))
    (d : JoinCocone F) (hd : IsColimitCone d) : IsColimitCone (mapJoinCocone U d) := by
  obtain ⟨H, hH, _, hcol⟩ := F1B.exists_kanLeftComma_candidate δ F hlocal
  exact colimitPreservation_of_relativeJoin δ F U H hH hcol
    (fun b ↦ relativeJoinFiber_isColimit_postcomp_of_local δ F U H hH b (hcol b) (hU b))
    hB d hd

end SerrePositivity.InfinityCategories.F2.Presentable
