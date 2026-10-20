module

public import SerrePositivity.InfinityCategories.F1.CocartesianCompStructLifting
public import SerrePositivity.InfinityCategories.F1.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.InvertibleCartesian
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianCancellation
public import SerrePositivity.InfinityCategories.F1B.KanIsofibrationCriterion

/-!
概要：quasicategory 上の cocartesian fibration は可逆辺を終点指定で持ち上げる。
方針：底の逆辺を始点指定で持ち上げ、逆の合成三角形を同じ底上へ充填する。
規約：元の辺の像と終点を厳密に保ち、追加の持ち上げ仮定は置かない。
使われ方：一般の cocartesian 標的への相対 Hom の制限同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 一般の cocartesian fibration は、可逆辺を元の像と指定した終点を保って持ち上げる。 -/
lemma cocartesianFibration_kanInvertibleTargetLifting {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] : F1B.KanInvertibleTargetLifting p := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  intro x e he ht
  have htarget : B.δ 0 (SSet.yonedaEquiv e) = p.app (Opposite.op ⦋0⦌) x := by
    have h := congrArg SSet.yonedaEquiv ht
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] at h
    exact h
  let b : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (B.δ 1 (SSet.yonedaEquiv e)) (p.app (Opposite.op ⦋0⦌) x) :=
    ⟨SSet.yonedaEquiv e, rfl, htarget⟩
  have hb : IsInvertibleEdge b := (isInvertibleEdge_congr
    (e := edgeOfSimplex (SSet.yonedaEquiv e)) (f := b) rfl).mp he
  obtain ⟨g, _, t₂⟩ := hb.nonempty_inverse
  have hgsrc : stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm g.edge =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm
      (show B.δ 1 g.edge = p.app (Opposite.op ⦋0⦌) x from g.src_eq)
  obtain ⟨H, hHsrc, hHp, hHc⟩ := CocartesianFibration.mem.2 x
    (SSet.yonedaEquiv.symm g.edge) hgsrc
  let y := E.δ 0 (SSet.yonedaEquiv H)
  have hsrc : E.δ 1 (SSet.yonedaEquiv H) = x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hHsrc, Equiv.apply_symm_apply]
  let f : SSet.Truncated.Edge (X := (truncation 2).obj E) x y :=
    ⟨SSet.yonedaEquiv H, hsrc, rfl⟩
  have hfp : p.app (Opposite.op ⦋1⦌) f.edge = g.edge := by
    change p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv H) = g.edge
    rw [← SSet.yonedaEquiv_comp, hHp, Equiv.apply_symm_apply]
  have hyp : p.app (Opposite.op ⦋0⦌) y = B.δ 1 (SSet.yonedaEquiv e) := by
    have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (0 : Fin 2)).op)
      (SSet.yonedaEquiv H)
    change p.app (Opposite.op ⦋0⦌) y = B.δ 0 (p.app (Opposite.op ⦋1⦌) f.edge) at hn
    rw [hfp] at hn
    exact hn.trans g.tgt_eq
  let k : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) y) (p.app (Opposite.op ⦋0⦌) x) :=
    ⟨b.edge, hyp.symm, htarget⟩
  have tb : SSet.Truncated.Edge.CompStruct (f.map ((truncation 2).map p)) k
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj E) x).map ((truncation 2).map p)) :=
    { simplex := t₂.simplex
      d₂ := t₂.d₂.trans hfp.symm
      d₀ := t₂.d₀
      d₁ := by
        change B.δ 1 t₂.simplex = p.app (Opposite.op ⦋1⦌) (E.σ 0 x)
        have hn := ConcreteCategory.congr_hom (p.naturality (SimplexCategory.σ (0 : Fin 1)).op) x
        change p.app (Opposite.op ⦋1⦌) (E.σ 0 x) = B.σ 0 (p.app (Opposite.op ⦋0⦌) x) at hn
        exact t₂.d₁.trans hn.symm }
  obtain ⟨k', t', ht'⟩ := cocartesianEdge_liftCompStruct p f hHc
    (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x) k tb
  have hkp : p.app (Opposite.op ⦋1⦌) k'.edge = b.edge := by
    rw [← t'.d₀]
    have hn := ConcreteCategory.congr_hom
      (p.naturality (SimplexCategory.δ (0 : Fin 3)).op) t'.simplex
    change p.app (Opposite.op ⦋1⦌) (E.δ 0 t'.simplex) =
      B.δ 0 (p.app (Opposite.op ⦋2⦌) t'.simplex) at hn
    rw [ht'] at hn
    exact hn.trans tb.d₀
  let T : (Δ[2] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm t'.simplex
  have hT : SSet.yonedaEquiv (X := E) (n := ⦋2⦌) T = t'.simplex := Equiv.apply_symm_apply _ _
  have hd₂ : E.δ 2 t'.simplex = f.edge := t'.d₂
  have hd₁ : E.δ 1 t'.simplex = (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x).edge := t'.d₁
  have hd₀ : E.δ 0 t'.simplex = k'.edge := t'.d₀
  have hfirst : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ T)) := by
    rw [stdSimplex.yonedaEquiv_δ_comp, hT, hd₂]
    exact hHc
  have hid : IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk
      (SSet.Truncated.Edge.id (X := (truncation 2).obj E) x))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hlong : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 1 ≫ T)) := by
    rw [stdSimplex.yonedaEquiv_δ_comp, hT, hd₁]
    exact isCocartesianEdge_of_isInvertibleEdge p _ hid
  have hkc : IsCocartesianEdge p k'.edge := by
    have h := kanIsCocartesianEdge_triangle_second_of_first_long T p hfirst hlong
    rw [stdSimplex.yonedaEquiv_δ_comp, hT, hd₀] at h
    exact h
  have hki : IsInvertibleEdge k' := isInvertibleEdge_of_isCocartesianEdge p k' hkc
    ((isInvertibleEdge_congr (e := k'.map ((truncation 2).map p)) (f := b) hkp).mpr hb)
  refine ⟨SSet.yonedaEquiv.symm k'.edge, ?_, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (show E.δ 0 k'.edge = x from k'.tgt_eq)
  · rw [SSet.yonedaEquiv_symm_comp, hkp]
    exact SSet.yonedaEquiv.symm_apply_apply e
  · rw [Equiv.apply_symm_apply]
    exact (isInvertibleEdge_congr (e := k') (f := edgeOfSimplex k'.edge) rfl).mp hki

/-- cocartesian fibration は単射な前合成同値を右に持ち上げる。追加の isofibration 仮定は不要。 -/
lemma cocartesianFibration_kanEquivalenceLifting {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] : F1B.KanEquivalenceLifting p := by
  letI : Quasicategory E := quasicategory_of_innerFibration p
  intro A D i hm hi
  exact F1B.kanEquivalenceLifting_of_innerFibration_of_targetLifting p
    (cocartesianFibration_kanInvertibleTargetLifting p) i hm hi

end SerrePositivity.InfinityCategories
