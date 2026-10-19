module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPinchedSlice

/-! # 固定標的の自然変換 prism の始域射影

概要：slice prism の始域は、係数を忘れた自然変換の始対象成分の辺で決まる。
方針：prism の前面への制限を自然変換の引き戻し自然性で計算する。
規約：全次数の写像の等式。使われ方：実分母の辺を保つ屋根 pullback への持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (C D : Type v) [DGCategory A C] [DGCategory A D]
variable {F G : DGFunctor A C D} (η : StrictNatTrans F G) (x y : C)

/-- 自然変換の指定対象における辺を、単体的写像として読む。 -/
def dgStrictNatTransPointMap : (Δ[1] : SSet.{max u v}) ⟶ dgNerve A D :=
  lift (SSet.const (Y := dgNerve A C) (Simplex.vertex x)) (𝟙 Δ[1]) ≫ η.homotopyMap

/-- slice の指定単体の始域は、元の係数単体の前面を二相で写した単体。 -/
lemma dgStrictNatTransPinchedSliceSimplex_projection {n : ℕ}
    (s : (DGNerve.pinchedHom A C x y) _⦋n⦌) (β : Fin (n + 1) →o Fin 2) :
    (sliceOverProjection _).app (Opposite.op ⦋n⦌)
      (dgStrictNatTransPinchedSliceSimplex A C D η x y s β) =
      η.simplex (PinchedHom.constant (X := dgNerve A C) (Simplex.vertex x) n) β := by
  let t := η.simplex s.val (pinchedPrismPhase β)
  have hp : (sliceOverProjection _).app (Opposite.op ⦋n⦌)
      (dgStrictNatTransPinchedSliceSimplex A C D η x y s β) =
      t.pullback Fin.castSuccOrderEmb.toOrderHom := by
    change SSet.yonedaEquiv (joinInl Δ[n] Δ[0] ≫
      ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm t)) = _
    rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl,
      SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
    rfl
  have hs : s.val.pullback Fin.castSuccOrderEmb.toOrderHom =
      PinchedHom.constant (X := dgNerve A C) (Simplex.vertex x) n := s.source
  have ht := (η.simplex_pullback s.val (pinchedPrismPhase β)
    Fin.castSuccOrderEmb.toOrderHom).symm
  exact hp.trans (ht.trans
    ((congrArg (η.simplex (s.val.pullback Fin.castSuccOrderEmb.toOrderHom))
      (pinchedPrismPhase_front β)).trans (congrArg (fun t => η.simplex t β) hs)))

/-- slice prism の始域への射影は、係数を忘れた始点の自然変換の辺。 -/
lemma dgStrictNatTransPinchedSlice_projection :
    dgStrictNatTransPinchedSlice A C D η x y ≫ sliceOverProjection _ =
      snd (DGNerve.pinchedHom A C x y) Δ[1] ≫ dgStrictNatTransPointMap A C D η x := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact dgStrictNatTransPinchedSliceSimplex_projection A C D η x y s.1
    (SSet.stdSimplex.objEquiv s.2).toOrderHom

end SerrePositivity.InfinityCategories
