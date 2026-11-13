module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.OrderedSimplexDiagonal

/-!
概要：射列と HA 単体の同時引き戻しに対して、対角評価が可換することを示す。
方針：既存の引き戻しの三分岐を使い、潰れた位置では元の恒等成分へ戻す。
規約：元の全退化を含む自然性であり、単射の面だけには制限しない。
使われ方：3b-3 R6、全パラメーター余錐族の単体的自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace OrderedSimplexFamily
variable {A : Type u} [CommRing A] {E : Type v} [DGCategory A E] {m n : ℕ}

/-- 同じ単調写像で射列の位置と HA 単体を同時に引き戻す。 -/
def pullback (d : OrderedSimplexFamily A E n) (α : Fin (m + 1) →o Fin (n + 1)) :
    OrderedSimplexFamily A E m where
  obj a := (d.obj (α a)).pullback α
  map a b hab := (d.map (α a) (α b) (α.monotone hab)).pullback α
  map_refl a := by
    rw [d.map_refl, StrictSimplexMap.pullback_id]
    rfl
  map_trans a b c hab hbc := by
    rw [← StrictSimplexMap.pullback_comp, d.map_trans]

/-- 潰れた同じ位置では、同じ閉零後合成は元の dg 単位へ戻る。 -/
lemma transport_unit_of_heq (d : OrderedSimplexFamily A E n) (p q : Fin (n + 1))
    (hpq : p ≤ q) {a b : Fin (n + 1)}
    (f : GradedHom A ((d.obj p).obj a) ((d.obj p).obj b) 0)
    (hp : p = q) (hab : a = b) (hf : HEq f (unitElement A ((d.obj p).obj b)).val) :
    HEq (d.transport p q hpq f) (unitElement A ((d.obj q).obj b)).val := by
  subst q
  subst b
  have hf' := eq_of_heq hf
  rw [hf', transport, d.map_refl]
  exact heq_of_eq (unit_compose A _)

/-- 対角の元の全 HA データは、面・退化を含む同時引き戻しに自然である。 -/
lemma diagonalData_pullback (d : OrderedSimplexFamily A E n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (d.pullback α).diagonalData = d.diagonalData.pullback α := by
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    change d.transport (α a) (α b) _
        (((d.obj (α a)).toSimplexData.pullback α).hom I a b k hI ha hb hk) =
      (d.diagonalData.pullback α).hom I a b k hI ha hb hk
    by_cases hi : Set.InjOn α (I : Set (Fin (m + 1)))
    · rw [Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      rfl
    · by_cases hc : I.card = 2
      · have hk0 : k = 0 := by omega
        subst hk0
        have hab : α a = α b := Index.collapse_two hi hc
          (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
        have hl := d.transport_unit_of_heq (α a) (α b) (le_of_eq hab) _ hab hab
          ((d.obj (α a)).toSimplexData.pullback_hom_of_collapsed_pair α I a b 0 hI ha hb hk hi hc)
        have hr := d.diagonalData.pullback_hom_of_collapsed_pair α I a b 0 hI ha hb hk hi hc
        exact eq_of_heq (hl.trans hr.symm)
      · rw [Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
          Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
        exact d.transport_zero _ _ _ _ _ _

/-- 対角の実単体も、全ての面・退化に自然である。 -/
lemma diagonal_pullback (d : OrderedSimplexFamily A E n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (d.pullback α).diagonal = d.diagonal.pullback α :=
  Simplex.ext (d.diagonalData_pullback α)

end OrderedSimplexFamily
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
