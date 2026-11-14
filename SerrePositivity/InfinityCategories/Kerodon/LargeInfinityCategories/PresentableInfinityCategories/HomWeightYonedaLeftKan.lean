module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightLocalColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightYonedaUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SliceComparison.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftHomUniversal

/-!
概要：元の Hom 前層の局所密度余極限を、元の持ち上げた関手に沿う左 Kan 局所図式へ移す。
方針：局所形状の宇宙比較で全余錐を再添字付けし、指定した頂点と普遍性を保つ。
規約：元の Hom 係数族との同型は、ここでは各頂点での結論に限る。
使われ方：P-12 の Yoneda 指定単位の局所普遍性と全自然比較の残りを明示する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


variable {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]

omit [Quasicategory C] in
/-- 概要：持ち上げた元の関手の実際の局所図式は、小さい局所 Yoneda 図式と一致する。
方針：局所形状の宇宙比較の射影則を使う。
規約：全図式の厳密な等式。使われ方：元の全余錐を実 Kan 局所図式へ移す。 -/
lemma homWeightLeftKanDiagram_universe (F : A ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} F c).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)
        (ULift.up c) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaDiagram F c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection]
  rfl

/-- 概要：局所密度余錐を、持ち上げた元の関手の実際の局所図式上へ移す。
方針：元の形状の宇宙同型の逆で再添字付けし、図式の一致を使う。
規約：元の Hom 前層を頂点に保つ。使われ方：左 Kan 存在の局所入力。 -/
def homWeightLeftKanDiagramCocone (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram ((SSet.uliftFunctor.{u + 1, u}).map F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) (ULift.up c)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} F c
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone F c).reindexIso e.symm
  refine ⟨d.val, d.property.trans ?_⟩
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagram_universe F c]
  change e.inv ≫ (e.hom ≫ _) = _
  rw [Iso.inv_hom_id_assoc]

/-- 概要：実局所 Kan 余錐の頂点は、元の Hom 係数族の指定値そのもの。
方針：再添字付けが余錐の右零単体を固定することを使う。
規約：元の係数族の値の等式。使われ方：全左 Kan 候補の値の計算。 -/
lemma homWeightLeftKanDiagramCocone_vertex (F : A ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone F c).vertex =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F).app (Opposite.op ⦋0⦌) (ULift.up c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} F c).inv (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone F c).val)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone_vertex F c

/-- 概要：元の Hom 係数を頂点とする実 Kan 局所余錐は余極限。
方針：密度余極限の普遍性を形状の厳密な同型で移す。
規約：C の余完備性を仮定しない。使われ方：Yoneda 図式の左 Kan 延長の存在。 -/
lemma homWeightLeftKanDiagramCocone_isColimit (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (homWeightLeftKanDiagramCocone F c) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso.{u, u + 1} F c
  have h := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_reindexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone F c) e.symm).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone_isColimit F c)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone F c).reindexIso e.symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone F c) rfl).mp h

/-- 概要：元の Yoneda 図式を元の F に沿って延長した任意の左 Kan 候補の値を計算する。
方針：指定単位の局所余極限と、構成した元の Hom 前層の余極限を比較する。
規約：これは対象ごとの同型。全自然な同型と区別する。
使われ方：全自然な比較射の局所可逆性の残りを検査する。 -/
def homWeightYonedaLeftKan_valueIso (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A}
    {β : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L)}
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L β) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (L.app (Opposite.op ⦋0⦌) (ULift.up c))
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F).app (Opposite.op ⦋0⦌) (ULift.up c)) := by
  let t := Classical.choose (hβ.colimitValue (ULift.up c))
  have ht := Classical.choose_spec (hβ.colimitValue (ULift.up c))
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso t (homWeightLeftKanDiagramCocone F c) ht.1
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone_isColimit F c)
  exact (eqToIso (congrArg HomotopyCategory.mk ht.2)).symm ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone_vertex F c))

/-- 概要：元の F に沿う Yoneda 左 Kan 延長が存在し、その各値は元の Hom 係数と同型。
方針：実局所図式の密度余極限を元の coherent な存在定理へ渡す。
規約：指定単位の候補はここで選ぶ。homWeightYonedaUnit の普遍性はまだ結論しない。
使われ方：P-12 の指定比較射の構成と、残る自然な可逆性の検査。 -/
lemma exists_homWeightYonedaLeftKan (F : A ⟶ C) :
    ∃ (L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A)
      (β : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)
        ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L β ∧
        ∀ c : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (L.app (Opposite.op ⦋0⦌) (ULift.up c))
          ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F).app (Opposite.op ⦋0⦌) (ULift.up c))) := by
  obtain ⟨L, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) (by
      rintro ⟨c⟩
      exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone F c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLeftKanDiagramCocone_isColimit F c⟩)
  exact ⟨L, β, hβ, fun c ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightYonedaLeftKan_valueIso F hβ c⟩⟩

variable (F : A ⟶ C)
    {L : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A}
    (β : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ L))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 1, u}).map F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) L β)

/-- 概要：指定左 Kan 候補から元の Hom 係数族への、元の Yoneda 単位を延長する実比較射。
方針：元の左 Kan の Hom 普遍性で構成済みの指定単位を一意に延長する。
規約：この射の可逆性はまだ主張しない。使われ方：元の単位の普遍性を局所可逆性で検査する。 -/
def homWeightYonedaLeftKanComparison : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom L (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
    β hβ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F)).surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightYonedaUnit F)).choose

/-- 概要：選んだ実比較射は構成済みの元の Yoneda 単位を正確に回収する。
方針：元の Hom 普遍性の全射性の仕様を取り出す。
規約：点ごとの同型を使って別の比較射へ置き換えない。
使われ方：指定単位の局所余錐と密度余錐の両立の検査。 -/
lemma homWeightYonedaLeftKanComparison_fac :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap ((SSet.uliftFunctor.{u + 1, u}).map F)
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy β))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F) (homWeightYonedaLeftKanComparison F β hβ) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightYonedaUnit F :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_homUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
    β hβ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F)).surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightYonedaUnit F)).choose_spec

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
