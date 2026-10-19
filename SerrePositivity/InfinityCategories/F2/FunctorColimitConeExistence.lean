module

public import SerrePositivity.InfinityCategories.F2.FunctorCoconePointwiseCriterion
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeOppositeExistence
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence

/-!
概要：点ごとの余極限の存在から関手圏の点ごとの余極限余錐を作る。
方針：指定評価を保つ反転同型で極限の存在へ移し、元の余錐へ戻す。
規約：元の図式と全ての評価点での普遍性を保持する。
使われ方：矢印圏の余極限錐と lax pullback の存在構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：各評価図式が余極限を持てば、全評価が余極限となる関手圏の余極限錐が存在する。
方針：反転した内部 Hom の点ごとの極限錐を作り、元の余錐の全射性で戻す。
規約：元の図式 r を厳密に固定する。
使われ方：Tamme Lemma 8(i) の矢印成分の存在。 -/
lemma exists_colimitCone_functor_of_pointwise {J K C : SSet.{u}} [Quasicategory C]
    (r : J ⟶ (ihom K).obj C)
    (hp : ∀ k : K _⦋0⦌, HasColimit (evaluateFunctorDiagram r k)) :
    ∃ c : JoinCocone r, IsColimitCone c ∧ ∀ k : K _⦋0⦌,
      IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt k) c) := by
  let e := HomotopyLimits.oppositeInternalHomIso K C
  let r' := SSet.opFunctor.map r ≫ e.hom
  have hr : HasPointwiseLimits r' := by
    intro k'
    obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k'
    change HasLimit ((SSet.opFunctor.map r ≫ e.hom) ≫
      evaluateFunctorAt (SSet.opObjEquiv.symm k))
    have he : (SSet.opFunctor.map r ≫ e.hom) ≫
        evaluateFunctorAt (SSet.opObjEquiv.symm k) =
          SSet.opFunctor.map (r ≫ evaluateFunctorAt k) := by
      rw [Category.assoc]
      change _ ≫ (HomotopyLimits.oppositeInternalHomIso K C).hom ≫
        evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
      rw [oppositeInternalHom_evaluate, CategoryTheory.Functor.map_comp]
    rw [he]
    obtain ⟨ck, hck⟩ := hp k
    exact ⟨F1B.kanCoconeReverseCone ck, (F1B.kanIsColimitCone_iff_reverseCone ck).1 hck⟩
  obtain ⟨d, hd⟩ := exists_pointwiseLimitCone r' hr
  have hback : r' ≫ e.inv = SSet.opFunctor.map r := by
    dsimp only [r']
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let d' := (mapJoinCone e.inv d).cast hback
  have hd' : IsLimitCone d' :=
    (((qCatEquivalenceOfIso e.symm).isLimitCone_iff d).1
      (isLimitCone_of_pointwise d hd)).cast hback
  obtain ⟨c, hc⟩ := F1B.kanCoconeReverseCone_surjective r d'
  have hval : (F1B.kanCoconeReverseCone c).val ≫ e.hom = d.val := by
    rw [hc]
    change (d.val ≫ e.inv) ≫ e.hom = d.val
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨c, (F1B.kanIsColimitCone_iff_reverseCone c).2 (hc.symm ▸ hd'), ?_⟩
  intro k
  apply (isLimitCone_reverse_postcomp_iff c (evaluateFunctorAt k)).1
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 (hd (SSet.opObjEquiv.symm k))
  change (F1B.kanCoconeReverseCone c).val ≫ SSet.opFunctor.map (evaluateFunctorAt k) =
    d.val ≫ evaluateFunctorAt (SSet.opObjEquiv.symm k)
  rw [← hval, Category.assoc]
  change _ = _ ≫ (HomotopyLimits.oppositeInternalHomIso K C).hom ≫
    evaluateFunctorAt (SSet.opObjEquiv.symm k)
  rw [oppositeInternalHom_evaluate]

end SerrePositivity.InfinityCategories.F2
