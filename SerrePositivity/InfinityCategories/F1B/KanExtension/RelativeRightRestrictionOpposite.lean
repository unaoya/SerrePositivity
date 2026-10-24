module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInternalHomOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeRightRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftKanRestrictionComparison
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorOppositeHom

/-!
概要：元の相対右 Kan 制限の反転を左 Kan 制限と同型で比較する。
方針：全部分複体の反転と内部 Hom の反転を、標準局所条件の双対判定でつなぐ。
規約：関手の族と相対標的の両方を全単体の同型として比較する。
使われ方：左の相対制限定理を元の右の相対制限へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：反転した関手頂点の右 Kan 条件は左 Kan 条件と同値。
方針：頂点を関手として表示し、内部 Hom の反転の頂点公式を使う。
規約：D と E のみ quasicategory とする。
使われ方：全部分圏の反転同型の頂点条件。 -/
lemma kanRelativeRightKanVertex_op_iff {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C)
    (x : ((ihom C).obj D).op _⦋0⦌) :
    KanRelativeRightKanVertex U δ (SSet.opObjEquiv x) ↔
      KanRelativeLeftKanVertex (SSet.opFunctor.map U) (SSet.opFunctor.map δ)
        ((HomotopyLimits.oppositeInternalHomIso C D).hom.app _ x) := by
  obtain ⟨F, hF⟩ := (functorVertexEquiv C D).surjective (SSet.opObjEquiv x)
  have hx : x = SSet.opObjEquiv.symm (functorVertex F) := by
    exact SSet.opObjEquiv.injective hF.symm
  rw [hx, SerrePositivity.InfinityCategories.F1B.oppositeInternalHom_vertex]
  change IsRelativeRightKanExtendedFrom U δ ((functorVertexEquiv C D).symm
    (functorVertex F)) ↔ IsRelativeLeftKanExtendedFrom _ _
      ((functorVertexEquiv C.op D.op).symm (functorVertex (SSet.opFunctor.map F)))
  have h₁ : (functorVertexEquiv C D).symm (functorVertex F) = F :=
    (functorVertexEquiv C D).symm_apply_apply F
  have h₂ : (functorVertexEquiv C.op D.op).symm
      (functorVertex (SSet.opFunctor.map F)) = SSet.opFunctor.map F :=
    (functorVertexEquiv C.op D.op).symm_apply_apply (SSet.opFunctor.map F)
  rw [h₁, h₂]
  exact kanIsRelativeRightKanExtendedFrom_iff_op_left U δ F

/-- 概要：右 Kan 関手の全部分圏の反転は反転後の左 Kan 関手の全部分圏と同型。
方針：全部分複体の反転同型と頂点条件に沿う内部 Hom の同型を合成する。
規約：関手を指定変換つきの別模型へ置き換えない。
使われ方：右の元の相対制限の始域の比較。 -/
def kanRelativeRightKanDiagramsOppositeIso {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) :
    (kanRelativeRightKanDiagrams U δ : SSet.{u}).op ≅
      (kanRelativeLeftKanDiagrams (SSet.opFunctor.map U) (SSet.opFunctor.map δ) : SSet.{u}) :=
  SerrePositivity.InfinityCategories.F1B.fullSubcomplexOppositeIso (KanRelativeRightKanVertex U δ) ≪≫
    fullSubcomplexIso (HomotopyLimits.oppositeInternalHomIso C D)
      (fun x ↦ KanRelativeRightKanVertex U δ (SSet.opObjEquiv x))
      (KanRelativeLeftKanVertex (SSet.opFunctor.map U) (SSet.opFunctor.map δ))
      (kanRelativeRightKanVertex_op_iff U δ)

/-- 概要：右の全部分圏の反転同型は関手圏への包含を保つ。
方針：二つの全部分複体同型の包含との可換性を合成する。
規約：単体写像の厳密な等式。
使われ方：相対制限の可換正方形の証明。 -/
lemma kanRelativeRightKanDiagramsOppositeIso_hom_ι {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) :
    (kanRelativeRightKanDiagramsOppositeIso U δ).hom ≫
      (kanRelativeLeftKanDiagrams (SSet.opFunctor.map U) (SSet.opFunctor.map δ)).ι =
    SSet.opFunctor.map (kanRelativeRightKanDiagrams U δ).ι ≫
      (HomotopyLimits.oppositeInternalHomIso C D).hom := by
  simp only [kanRelativeRightKanDiagramsOppositeIso, Iso.trans_hom,
    kanRelativeLeftKanDiagrams, kanRelativeRightKanDiagrams, Category.assoc,
    fullSubcomplexIso_hom_ι]
  rw [← Category.assoc, SerrePositivity.InfinityCategories.F1B.fullSubcomplexOppositeIso_hom_ι]

/-- 概要：元の相対右 Kan 制限の反転は左 Kan 制限と可換正方形をなす。
方針：始域の包含と相対内部 Hom の比較の二つの可換性を合成する。
規約：両側の相対内部 Hom の引き戻しの選択を明示する。
使われ方：左の制限の充満忠実性と自明 Kan 性の右への移送。 -/
lemma kanRelativeRightKanRestriction_opposite_square {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U)
    (t : internalHom.PullbackObjObj (SSet.opFunctor.map δ) (SSet.opFunctor.map U)) :
    (kanRelativeRightKanDiagramsOppositeIso U δ).hom ≫
      kanRelativeLeftKanRestriction (SSet.opFunctor.map U) (SSet.opFunctor.map δ) t =
    SSet.opFunctor.map (kanRelativeRightKanRestriction U δ s) ≫
      (kanRelativeInternalHomOppositeIso δ U s t).hom := by
  simp only [kanRelativeLeftKanRestriction, ← Category.assoc,
    kanRelativeRightKanDiagramsOppositeIso_hom_ι]
  rw [Category.assoc, kanRelativeInternalHomOppositeIso_comparison,
    ← Category.assoc, ← Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.F1B
