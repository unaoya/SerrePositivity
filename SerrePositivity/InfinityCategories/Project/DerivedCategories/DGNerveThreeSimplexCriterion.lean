module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveThreePointIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTripleBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTetrahedronBoundary
/-!
概要：同じ辺・三点・四点 cochain の微分式から全 HA 方程式を持つ三単体を構成する。
方針：濃度二・三・四で分け、元の全 Hom 族を保って方程式を回収する。
規約：必要な微分式は明示した実成分の等式。使われ方：tensor 候補の三単体への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 指定した全低次微分式から、同じデータを持つ実三単体を作る。 -/
def dgNerveThreeSimplex_of_equations (d : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D 3)
    (he : ∀ (a b : Fin 4) (hab : a < b), _root_.SerrePositivity.DifferentialGraded.differential R (d.edgeHom a b hab) = 0)
    (ht : ∀ (a b c : Fin 4) (hab : a < b) (hbc : b < c),
      _root_.SerrePositivity.DifferentialGraded.differential R (d.tripleHom a b c hab hbc) =
        _root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (d.edgeHom b c hbc) (d.edgeHom a b hab) (by decide) -
          d.edgeHom a c (hab.trans hbc))
    (hq : differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTetrahedronHom R D d) =
      d.rhs Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D 3 where
  toSimplexData := d
  equation I a b k hI ha hb hk := by
    have hle := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hle
    have haI : IsLeast (I : Set (Fin 4)) a := by rw [ha]; exact I.isLeast_min' _
    have hbI : IsGreatest (I : Set (Fin 4)) b := by rw [hb]; exact I.isGreatest_max' _
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card (by omega)
      simpa only [← ha, ← hb] using h
    by_cases h4 : I.card = 4
    · have hu : I = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [h4])
      subst I
      have ha' : a = 0 :=
        ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
      have hb' : b = 3 :=
        hb.trans ((Finset.max'_eq_iff _ _ 3).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
      have hk' : k = -2 := by simpa using hk
      subst ha' hb' hk'
      exact hq
    · by_cases h2 : I.card = 2
      · have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair h2 haI hbI
        have hk' : k = 0 := by omega
        subst hk'
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_of_card_two _ _ _ _ _ _ _ _ _ h2]
        subst I
        exact he a b hab
      · have h3 : I.card = 3 := by omega
        obtain ⟨c, htriple, hac, hcb⟩ :=
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveIndex_eq_triple_of_card_three I a b h3 haI hbI
        have hk' : k = -1 := by omega
        subst hk'
        subst I
        rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTriple_rhs R D d a c b hac hcb]
        exact ht a c b hac hcb
end SerrePositivity.InfinityCategories.Project.DerivedCategories
