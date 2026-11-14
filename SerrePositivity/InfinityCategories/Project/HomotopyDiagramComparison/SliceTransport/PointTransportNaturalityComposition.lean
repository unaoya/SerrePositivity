module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorIsoPointEvaluation

/-!
概要：一点評価した指定同型を使い、輸送比較の自然性から終点の合成式を得る。
方針：一点評価と後合成の可換性、Arrow の端点移送、自然性の正方形を組み合わせる。
規約：標準側が恒等であることは証明として受け取る。使われ方：左比較の終点の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma arrow_comp_congr {C : Type*} [Category* C] {a b c a' b' c' : C}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  subst a' b'
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst c'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  subst f' g'
  rfl

private lemma arrow_comp_right_identity {C : Type*} [Category* C] {a b c d : C}
    (f : a ⟶ b) (g : b ⟶ c) (hg : Arrow.mk g = Arrow.mk (𝟙 d)) :
    Arrow.mk (f ≫ g) = Arrow.mk f := by
  obtain ⟨hb, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst d c
  simp only [eqToHom_refl, Category.comp_id] at hg
  subst g
  rw [Category.comp_id]

/-- 一点の関手空間の評価は、元の射による後合成と厳密に可換。 -/
lemma pointFunctorEvaluation_postcomp {X Y : SSet.{u}} (R : X ⟶ Y) :
    (ihom (Δ[0] : SSet.{u})).map R ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom ≫ R := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 同じ一点の同型を後合成して評価しても、評価してから後合成した射と一致する。 -/
lemma pointFunctorIso_postcomp_hom_arrow {X Y : SSet.{u}}
    {f g : (Δ[0] : SSet.{u}) ⟶ X} (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (R : X ⟶ Y) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp I R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom).hom =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom) R).hom := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp I R = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I ((ihom (Δ[0] : SSet.{u})).map R) := by
    apply Iso.ext
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, eqToIso_refl, Iso.refl_symm, hoFunctor_obj, Cat.of_α,
      hoFunctor_map, Functor.toCatHom_toFunctor, mapHomotopyCategory_obj_mk, Iso.trans_refl,
      Iso.trans_hom, Iso.refl_hom, Functor.mapIso_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map]
    exact Category.id_comp _
  rw [hp]
  have hl := congrArg (fun J ↦ Arrow.mk J.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp I ((ihom (Δ[0] : SSet.{u})).map R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom)
  have hr := congrArg (fun J ↦ Arrow.mk J.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom R)
  have hm := congrArg (fun k : (ihom (Δ[0] : SSet.{u})).obj X ⟶ Y ↦
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I k).hom) (pointFunctorEvaluation_postcomp R)
  exact hl.trans (hm.trans hr.symm)

/-- 輸送比較の標準成分が恒等なら、終点の像は実際の成分と始点の像の合成。 -/
lemma functorIso_naturality_pointComposition {A X Y : SSet.{u}}
    (F : A ⟶ X) (G : A ⟶ Y) (R : X ⟶ Y) (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso G (F ≫ R))
    {x y : A _⦋0⦌} (s : A.Edge x y)
    {f₀ f₁ : (Δ[0] : SSet.{u}) ⟶ X} (J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f₀ f₁)
    {g₀ : (Δ[0] : SSet.{u}) ⟶ Y} (K : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g₀ (f₀ ≫ R))
    (hJ : Arrow.mk ((hoFunctor.map F).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk s.toTruncated)) =
        Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map J (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).hom)
    (hK : Arrow.mk (I.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom).hom)
    (w : hoFunctor.obj Y)
    (hy : Arrow.mk (I.toNatIso.hom.app (SSet.HomotopyCategory.mk y)) = Arrow.mk (𝟙 w)) :
    Arrow.mk ((hoFunctor.map G).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk s.toTruncated)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (K ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp J R)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom).hom := by
  let t := SSet.Truncated.HomotopyCategory.homMk s.toTruncated
  have hm := congrArg (fun H ↦ H.mapArrow.obj (Arrow.mk t))
    congr($(hoFunctor.map_comp F R).toFunctor)
  have hr : Arrow.mk ((hoFunctor.map (F ≫ R)).toFunctor.map t) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp J R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom).hom :=
    hm.trans ((congrArg (hoFunctor.map R).toFunctor.mapArrow.obj hJ).trans
      (pointFunctorIso_postcomp_hom_arrow J R).symm)
  have hn := I.toNatIso.hom.naturality t
  have hc := (arrow_comp_right_identity
    ((hoFunctor.map G).toFunctor.map t) (I.toNatIso.hom.app (SSet.HomotopyCategory.mk y)) hy).symm
  refine hc.trans ((congrArg Arrow.mk hn).trans ?_)
  refine (arrow_comp_congr hK hr).trans ?_
  exact (congrArg (fun J ↦ Arrow.mk J.hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_trans K (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp J R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom)).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
