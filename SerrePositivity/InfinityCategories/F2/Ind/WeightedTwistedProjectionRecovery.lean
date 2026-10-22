module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTwistedProjections

/-!
概要：twisted-arrow 引き戻しの weighted 単体は、元の二つの全射影で決まる。
方針：定値な底への自然性で最後の値から全初区間を回収し、引き戻しの両射影を比較。
規約：元の全係数を保持。使われ方：同じ weighted 全空間の引き戻し性の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 定値な twisted-arrow 底の各初区間は、最後の同じ底の単体の制限。 -/
lemma weightedTwistedCoefficient_fst {n : ℕ}
    (s : weightedNerveSimplex (strictRightTwistedElementsDiagram F) n) (i : Fin (n + 1)) :
    s.2.app i ≫ pullback.fst (edgewiseRight C) (F.obj (s.1.obj i)).val.hom =
      SSet.stdSimplex.map (simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
        (s.2.app (Fin.last n) ≫ pullback.fst _ _) := by
  have h := (s.2 ≫ Functor.whiskerLeft s.1
    (strictRightTwistedBaseProjection F)).naturality (homOfLE (Fin.le_last i))
  change SSet.stdSimplex.map (simplexPrefixInclusion i.val n _) ≫
      (s.2.app (Fin.last n) ≫ pullback.fst _ _) =
    (s.2.app i ≫ pullback.fst _ _) ≫ 𝟙 _ at h
  exact (h.trans (Category.comp_id _)).symm

/-- 元の全 twisted-arrow 単体は、元の底と全空間の二つの射影で一意に決まる。 -/
lemma weightedTwistedProjections_jointlyInjective (n : ℕ) :
    Function.Injective (fun s : (weightedNerve (strictRightTwistedElementsDiagram F)) _⦋n⦌ ↦
      ((weightedTwistedBaseProjection F).app _ s,
        (weightedTwistedTotalProjection F).app _ s)) := by
  rintro ⟨σ, τ⟩ ⟨σ', τ'⟩ h
  have hb := congrArg Prod.fst h
  have he := congrArg Prod.snd h
  change (⟨σ, τ ≫ Functor.whiskerLeft σ (strictRightTwistedTotalProjection F)⟩ :
      weightedNerveSimplex (rightFibrationTotalDiagram F) n) =
    ⟨σ', τ' ≫ Functor.whiskerLeft σ' (strictRightTwistedTotalProjection F)⟩ at he
  have hσ := (Sigma.mk.inj he).1
  cases hσ
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  apply pullback.hom_ext
  · change SSet.yonedaEquiv (τ.app (Fin.last n) ≫ pullback.fst _ _) =
      SSet.yonedaEquiv (τ'.app (Fin.last n) ≫ pullback.fst _ _) at hb
    have ht := SSet.yonedaEquiv.injective hb
    exact (weightedTwistedCoefficient_fst F ⟨σ, τ⟩ i).trans
      ((congrArg (fun q ↦ SSet.stdSimplex.map
        (simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫ q) ht).trans
          (weightedTwistedCoefficient_fst F ⟨σ, τ'⟩ i).symm)
  · exact NatTrans.congr_app (eq_of_heq (Sigma.mk.inj he).2) i

end SerrePositivity.InfinityCategories.F2.Ind
