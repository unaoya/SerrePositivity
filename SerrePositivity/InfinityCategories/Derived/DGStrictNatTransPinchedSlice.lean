module
public import SerrePositivity.InfinityCategories.Derived.PinchedPrismPhase
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans
public import SerrePositivity.InfinityCategories.DGNerve.PinchedComponents

/-! # 厳密 dg 自然変換の固定標的 slice prism

概要：元の pinched Hom の全単体と時刻から、終点を固定した実 slice の単体を作る。
方針：前面の時刻を最終相一へ延長し、厳密自然変換の単体へ適用する。
規約：全ての面・退化に自然。使われ方：閉前合成の実屋根への全次数の移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [DGCategory A C] [DGCategory A D]
variable {F G : DGFunctor A C D} (η : StrictNatTrans F G) (x y : C)

/-- 係数単体と時刻から、最後の標的を G(y) に固定した実 slice 単体を得る。 -/
def dgStrictNatTransPinchedSliceSimplex {n : ℕ}
    (s : (DGNerve.pinchedHom A C x y) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm
      (Simplex.vertex (G.obj y)))) _⦋n⦌ :=
  ⟨(joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    (η.simplex s.val (pinchedPrismPhase β)), by
    rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
      SSet.yonedaEquiv_symm_naturality_left]
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply (dgNerve.vertexEquiv A D).injective
    change StrictNatTrans.phaseObj F G (pinchedPrismPhase β (Fin.last (n + 1)))
      (s.val.obj (Fin.last (n + 1))) = G.obj y
    rw [pinchedPrismPhase_last, DGNerve.PinchedHom.target_obj s]
    rfl⟩

/-- 全係数と全時刻を持つ、指定終点の実 slice への単体的 prism。 -/
def dgStrictNatTransPinchedSlice : DGNerve.pinchedHom A C x y ⊗ (Δ[1] : SSet.{max u v}) ⟶
    sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex (G.obj y))) where
  app _ := ↾fun s => dgStrictNatTransPinchedSliceSimplex A C D η x y s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    let β := (SSet.stdSimplex.objEquiv s.2).toOrderHom
    change (joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
      (η.simplex (s.1.val.pullback (PinchedHom.extend α.unop).toOrderHom)
        (pinchedPrismPhase (β.comp α.unop.toOrderHom))) =
      joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (η.simplex s.1.val (pinchedPrismPhase β)))
    let t := η.simplex s.1.val (pinchedPrismPhase β)
    have ht : η.simplex (s.1.val.pullback (PinchedHom.extend α.unop).toOrderHom)
        (pinchedPrismPhase (β.comp α.unop.toOrderHom)) =
        t.pullback (PinchedHom.extend α.unop).toOrderHom :=
      (congrArg (η.simplex (s.1.val.pullback (PinchedHom.extend α.unop).toOrderHom))
        (pinchedPrismPhase_comp β α.unop.toOrderHom)).trans
          (η.simplex_pullback s.1.val (pinchedPrismPhase β)
            (PinchedHom.extend α.unop).toOrderHom)
    refine (congrArg (fun t : Simplex A D (m + 1) => (joinStdSimplexIso m 0).hom ≫
      (SSet.yonedaEquiv (X := dgNerve A D)).symm t) ht).trans ?_
    change (joinStdSimplexIso m 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
      ((dgNerve A D).map (PinchedHom.extend α.unop).op t) =
      joinMap (SSet.stdSimplex.map α.unop) (𝟙 Δ[0]) ≫
        ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm t)
    rw [← SSet.yonedaEquiv_symm_naturality_left, ← Category.assoc]
    exact congrArg (fun f => f ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm t)
      (joinStdSimplexIso_rightPoint_naturality α.unop).symm


end SerrePositivity.InfinityCategories
