module

public import SerrePositivity.InfinityCategories.F1B.KanComparisonCartesian
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：左 Kan の局所余錐の輸送を h Fun の射として制限・評価する公式。
方針：指定変換上の辺と頂点固定の辺を、それぞれ代表一次単体で同定する。
規約：輸送は任意の選択を許す。
使われ方：二つの左 Kan 拡張間の比較射の局所可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所余錐の輸送の制限は指定 Kan 変換の局所添字への制限を表す。
方針：輸送の図式固定式を curry し、両端の余錐の制限の等式で輸送する。
規約：制限した射そのものの式であり、別の比較射を選ばない。
使われ方：局所比較正方形の底での可換性。 -/
lemma kanLeftTransport_restriction_hom {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    (hoFunctor.map (coconeRestriction (leftKanShape δ c) D)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk t.edge) =
      eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q)) t.cocone.property) ≫
        (hoFunctor.map ((pre (leftKanProjection δ c)).app D)).toFunctor.map
          (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) ≫
        eqToHom (congrArg (fun q ↦ HomotopyCategory.mk (functorVertex q))
          (leftKanCanonicalCocone δ F c).property).symm := by
  have he : (t.edge.map ((truncation 2).map (coconeRestriction (leftKanShape δ c) D))).edge =
      (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPrecomp β (leftKanProjection δ c))).edge := by
    change SSet.yonedaEquiv (curry ((β_ _ Δ[1]).hom ≫ t.family) ≫
        coconeRestriction (leftKanShape δ c) D) =
      SSet.yonedaEquiv (curry ((leftKanProjection δ c ▷ Δ[1]) ≫ β.h))
    congr 1
    apply uncurry_injective
    dsimp only [coconeRestriction]
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    change (β_ (leftKanShape δ c) Δ[1]).hom ≫
      (Δ[1] ◁ joinInl (leftKanShape δ c) Δ[0]) ≫ t.family = _
    rw [t.diagram, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have h := homMk_transport (congrArg functorVertex t.cocone.property)
    (congrArg functorVertex (leftKanCanonicalCocone δ F c).property)
    (t.edge.map ((truncation 2).map (coconeRestriction (leftKanShape δ c) D)))
    (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp β (leftKanProjection δ c))) he
  rw [functorHomotopyPrecomp_hom] at h
  rw [← h]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：左比較余錐の輸送は余錐の頂点で可逆な射を与える。
方針：頂点固定式の一次単体を定値辺と同定する。
規約：輸送を選び直さず、指定した t の辺を評価する。
使われ方：局所比較正方形から底圏の比較射の可逆性を得る。 -/
lemma kanLeftTransport_apex_isIso {K C D : SSet.{u}} {δ : K ⟶ C}
    {F₀ : K ⟶ D} {F : C ⟶ D} {β : SSet.Homotopy F₀ (δ ≫ F)} {c : C _⦋0⦌}
    (t : LeftKanCoconeTransport δ F₀ F β c) :
    IsIso ((hoFunctor.map (coconeApexEvaluation (leftKanShape δ c) D)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk t.edge)) := by
  let z := (leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋0⦌)
    ((joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  have he : (t.edge.map ((truncation 2).map
      (coconeApexEvaluation (leftKanShape δ c) D))).edge = PinchedHom.constant z 1 := by
    let w : ((Δ[1] : SSet.{u}) ⊗ Δ[0]) _⦋1⦌ :=
      ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
        PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1⟩
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app t.fixedVertex (Opposite.op ⦋1⦌)) w
    change t.family.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 Δ[1]),
          (joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
            (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) =
      (leftKanCanonicalCocone δ F c).val.app (Opposite.op ⦋1⦌)
        ((joinInr (leftKanShape δ c) (Δ[0] : SSet.{u})).app (Opposite.op ⦋1⦌)
          (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1)) at h
    rw [pinchedConstant_map, pinchedConstant_map] at h
    exact h
  have hi := isEquivalencePathVertex_const z
  unfold IsEquivalencePathVertex at hi
  rw [intervalFunctorVertexEdge_functorVertex] at hi
  exact (isInvertibleEdge_congr he).2 hi

end SerrePositivity.InfinityCategories.F1B
