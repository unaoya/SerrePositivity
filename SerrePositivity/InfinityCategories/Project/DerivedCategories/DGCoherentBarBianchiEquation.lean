module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBianchiFullEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataRhsComponents

/-!
概要：実 bar の全ての末端部分集合で、HA 右辺は同じ θ による作用に等しい。
方針：先頭部分集合の昇順列挙を取り、実データの単射自然性で全体の式を移す。
規約：MC 方程式も filtered 性も仮定しない。
使われ方：無条件の bar MC の Bianchi 判定への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

private lemma rhs_indices_heq {A : Type u} [CommRing A] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A C]
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A C n)
    {I J : Finset (Fin (n + 1))} {a b c d : Fin (n + 1)} {k l : ℤ}
    {hI : 2 ≤ I.card} {ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)}
    {hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)} {hk : k = 2 - (I.card : ℤ)}
    {hJ : 2 ≤ J.card} {hc : c = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)}
    {hd : d = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)} {hl : l = 2 - (J.card : ℤ)}
    (hIJ : I = J) (hac : a = c) (hbd : b = d) (hkl : k = l) :
    HEq (s.rhs I a b k hI ha hb hk) (s.rhs J c d l hJ hc hd hl) := by
  subst J
  subst c
  subst d
  subst l
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarBianchiData_rhs {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).rhs J a (Fin.last (n + 1)) k hJ ha hb hk =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiTheta R D F σ)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ).hom J a (Fin.last (n + 1)) k hJ ha hb hk) rfl := by
  let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ
  have hLast : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J
  have hK : K.Nonempty := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hLast
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  let α := (K.orderEmbOfFin hc).toOrderHom
  have hα : Function.Injective α := (K.orderEmbOfFin hc).injective
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α
  have hβ : Function.Injective β := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarExtend_injective α hα
  let τ := I.map (SimplexCategory.mkHom α).op σ
  have him : (Finset.univ : Finset (Fin (r + 2))).image β = J := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBar_withLast_univ r, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_withLast_extend]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast
      ((Finset.univ : Finset (Fin (r + 1))).image (K.orderEmbOfFin hc)) = J
    rw [K.image_orderEmbOfFin_univ hc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast_withoutLast J hLast
  have hA : β 0 = a := by
    rw [ha]
    have h0 : IsLeast ((Finset.univ : Finset (Fin (r + 2))) : Set (Fin (r + 2))) 0 :=
      ⟨Finset.mem_univ _, fun i _ => Fin.zero_le i⟩
    simpa only [him] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (f := β) β.monotone h0
      (Finset.Nonempty.image Finset.univ_nonempty β)
  have hcardJ : J.card = r + 2 := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast J hLast
    change J.card = K.card + 1 at hh
    omega
  have hkr : k = -(r : ℤ) := by rw [hcardJ] at hk; omega
  have hNat := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_map R D F σ α hα
  have hRhs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_heq_of_eq hNat Finset.univ 0 (Fin.last (r + 1))
    (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hβ.injOn] at hRhs
  have hRhsAny : HEq (s.rhs J a (Fin.last (n + 1)) k hJ ha hb hk)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F τ).rhs Finset.univ 0 (Fin.last (r + 1))
        (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)) := by
    refine HEq.trans ?_ hRhs.symm
    exact rhs_indices_heq s him.symm hA.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α).symm hkr
  have hHom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq hNat Finset.univ 0 (Fin.last (r + 1))
    (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hβ.injOn] at hHom
  have hHomAny : HEq (s.hom J a (Fin.last (n + 1)) k hJ ha hb hk)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F τ).hom Finset.univ 0 (Fin.last (r + 1))
        (-(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card r) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min r)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max r) (by simp; omega)) := by
    refine HEq.trans ?_ hHom.symm
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree s him.symm hA.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α).symm hkr
  have hHomFinal := hHomAny.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_hom_univ_heq R D F τ)
  have hRhsFinal := hRhsAny.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_full_rhs_heq_theta_all R D F τ)
  have hobj0 : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F τ).obj 0 = s.obj a :=
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) (r + 1) => t.obj 0) hNat).trans
      (congrArg s.obj hA)
  have hx : s.obj a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨r, τ⟩ := hobj0.symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_castSucc R D F τ 0).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F τ 0))
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData_obj_last R D F σ
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    (p := k) (q := 1) (k := k + 1) (p' := -(r : ℤ)) (q' := 1) (k' := -(r : ℤ) + 1)
    hx hy hy hkr rfl (by omega) _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiTheta_heq R D F σ) hHomFinal rfl rfl
  exact eq_of_heq (hRhsFinal.trans hcomp.symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
