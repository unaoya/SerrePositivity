module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveInnerFibration
public import SerrePositivity.InfinityCategories.F1.WeightedNerveEdgeCoefficient
public import SerrePositivity.InfinityCategories.F1.CartesianEdge
public import SerrePositivity.InfinityCategories.F1.TautScaffold
public import SerrePositivity.InfinityCategories.F1.CoreFaces
public import SerrePositivity.InfinityCategories.Core.OuterHornDuality

/-!
概要：最後の係数が可逆な weighted nerve の辺は cocartesian。
方針：相対外ホーンを最後の係数へ写し、可逆な初辺を使って充填して戻す。
規約：係数は quasicategory。Kan 性は要求しない。
使われ方：Cat∞ 値 weighted nerve の標準水平辺と cocartesian fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 最後の係数で可逆な辺を持つ元の weighted nerve の辺は cocartesian。 -/
lemma isCocartesianEdge_weightedNerve_of_coefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (e : (weightedNerve F) _⦋1⦌) (he : WeightedNerveCoefficientInvertible F e) :
    IsCocartesianEdge (weightedNerveProjection F) e := by
  intro n a b hea sq
  let σ := SSet.yonedaEquiv b
  have hb : SSet.yonedaEquiv.symm σ = b := SSet.yonedaEquiv.symm_apply_apply _
  have ha : a ≫ weightedNerveProjection F =
      (horn (n + 2) 0).ι ≫ SSet.yonedaEquiv.symm σ := by rw [hb]; exact sq.w
  let q := weightedNerveHornLastCoefficient F σ 0 a ha
  have hi : IsInvertibleEdge (edgeOfSimplex (q.app _ (initialHornEdge n))) := by
    apply weightedNerveSimplexCoefficient_edge_invertible F σ a (horn (n + 2) 0).ι ha
    rw [hea]
    exact he
  have hk : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  obtain ⟨H₀, hH₀⟩ := hasInitialHornFillers_of_isInvertibleEdge
    (edgeOfSimplex (q.app _ (initialHornEdge n))) hi n q rfl
  obtain ⟨H, hH, hHp⟩ := exists_weightedNerveHorn_lift_of_coefficient_filler
    F σ 0 hk a ha ⟨H₀, hH₀⟩
  exact CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := hHp.trans hb }

/-- taut scaffold の標準水平辺は、最後の係数で退化辺を持つため cocartesian。 -/
lemma tautScaffold_horizontal_isCocartesianEdge {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] {c d : C}
    (f : c ⟶ d) (x : (F.obj c) _⦋0⦌) :
    IsCocartesianEdge (weightedNerveProjection F)
      ((tautScaffold F).app _ ⟨ComposableArrows.mk₁ f, SSet.const x⟩) := by
  apply isCocartesianEdge_weightedNerve_of_coefficient
  change IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv
    (stdSimplex.map (simplexPrefixInclusion 1 1 _) ≫ SSet.const x ≫
      F.map ((ComposableArrows.mk₁ f).map (homOfLE (Fin.zero_le (Fin.last 1)))))))
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp,
    SSet.const_comp]
  exact isInvertibleEdge_map_const _ 0

end SerrePositivity.InfinityCategories
