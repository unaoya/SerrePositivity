module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftTransportHom
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：左 Kan 余錐の輸送の底での成分と指定単位の成分の可逆性を比較する。
方針：図式への制限の公式を固定頂点で評価し、端点の等式による同型を消去する。
規約：輸送の選択と指定変換を変更しない。
使われ方：恒等射での局所余錐の脚から元の Kan 単位へ可逆性を戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：二胞体の成分の可逆性は端点を輸送する前の評価でも判定できる。
方針：端点の等式の同型による前後合成を消去する。
規約：始域と標的の quasicategory 性は不要。
使われ方：局所輸送の制限の式を固定頂点で評価する。 -/
lemma kanFunctorHomEvaluate_isIso_iff {A D : SSet.{u}} {F G : A ⟶ D}
    (α : FunctorHom F G) (a : A _⦋0⦌) :
    IsIso (functorHomEvaluate α a) ↔
      IsIso ((hoFunctor.map (evaluateFunctorAt (Y := D) a)).toFunctor.map α) := by
  simp only [functorHomEvaluate, isIso_comp_left_iff, isIso_comp_right_iff]

/-- 概要：輸送の底での成分の可逆性は元の指定単位の対応する成分の可逆性と同値。
方針：余錐の制限の二胞体の式を評価し、端点の輸送を同型として消去する。
規約：局所添字の頂点 a は任意。
使われ方：像の点の恒等射で指定 Kan 単位を評価する。 -/
lemma kanLeftTransport_source_component_isIso_iff {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) (a : (leftKanShape δ c) _⦋0⦌) :
    IsIso (functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk t.edge)
      ((joinInl (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) a)) ↔
    IsIso (functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
      ((leftKanProjection δ c).app (Opposite.op ⦋0⦌) a)) := by
  rw [← functorHomEvaluate_precomp (SSet.Truncated.HomotopyCategory.homMk t.edge)
    (joinInl (leftKanShape δ c) (Δ[0] : SSet.{u})) a]
  change IsIso (functorHomEvaluate (U := joinInl _ _ ≫ t.cocone.val)
    (V := joinInl _ _ ≫ (leftKanCanonicalCocone δ F c).val)
    ((hoFunctor.map (coconeRestriction (leftKanShape δ c) D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk t.edge)) a) ↔ _
  rw [kanFunctorHomEvaluate_isIso_iff, kanLeftTransport_restriction_hom]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map,
    isIso_comp_left_iff, isIso_comp_right_iff]
  let γ : FunctorHom (leftKanProjection δ c ≫ F₀) (leftKanProjection δ c ≫ (δ ≫ F)) :=
    (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
  exact (kanFunctorHomEvaluate_isIso_iff γ a).symm.trans
    (Iff.of_eq (congrArg IsIso (functorHomEvaluate_precomp
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))
      (leftKanProjection δ c) a)))

end SerrePositivity.InfinityCategories.F1B
