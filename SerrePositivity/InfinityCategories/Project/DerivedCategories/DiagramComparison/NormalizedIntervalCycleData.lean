module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalCochain
/-!
概要：閉零次値とその境界をsmart切断の区間データへ送る。
方針：既存のcyclesへの持ち上げと切断の項同型を使う。
規約：A06の同じ証明の分割。閉性と境界の式を型に保持する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (H : CochainComplex (ModuleCat.{u} A) ℤ)
/-- 閉零次値をsmart切断の零次の値へ送る。 -/
def intervalTruncCycle (z : H.X 0) (hz : H.d 0 1 z = 0) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0 := by
  let k : ModuleCat.of A A ⟶ H.X 0 := ModuleCat.ofHom (LinearMap.toSpanSingleton A (H.X 0) z)
  have hk : k ≫ H.d 0 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change H.d 0 1 (r • z) = 0
    rw [map_smul, hz, smul_zero]
  exact (H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0) (i := 0) (i' := 0)
    (by simp) ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).inv
      ((H.liftCycles k 1 (by simp) hk) (1 : A))
/-- 次数−1の値を同じ切断の一次の値へ送る。 -/
def intervalTruncEdge (w : H.X (-1)) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 1 :=
  (H.truncLE'XIso (ComplexShape.embeddingUpIntLE 0) (i := 1) (i' := -1)
    (by simp) (by rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]; decide)).inv w
/-- 切断の零次の値をcyclesの包含で戻すと元の閉じた値になる。 -/
theorem intervalTruncCycle_value (z : H.X 0) (hz : H.d 0 1 z = 0) :
    H.iCycles 0 ((H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
      (i := 0) (i' := 0) (by simp)
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)).hom
      (intervalTruncCycle A H z hz)) = z := by
  dsimp only [intervalTruncCycle]
  rw [Iso.inv_hom_id_apply]
  erw [← ModuleCat.comp_apply, H.liftCycles_i]
  change (1 : A) • z = z
  exact one_smul A z

/-- 境界の式は同じsmart切断でも保たれる。 -/
theorem intervalTrunc_boundary (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0 (intervalTruncEdge A H w) =
      intervalTruncCycle A H y hy - intervalTruncCycle A H x hx := by
  let e0 := H.truncLE'XIsoCycles (ComplexShape.embeddingUpIntLE 0)
    (i := 0) (i' := 0) (by simp)
    ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl)
  let i := e0.hom ≫ H.iCycles 0
  haveI : Mono i := by dsimp only [i]; infer_instance
  apply (ModuleCat.mono_iff_injective i).mp inferInstance
  change H.iCycles 0 (e0.hom ((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).d 1 0
    (intervalTruncEdge A H w))) =
    H.iCycles 0 (e0.hom (intervalTruncCycle A H y hy - intervalTruncCycle A H x hx))
  erw [map_sub, map_sub, intervalTruncCycle_value, intervalTruncCycle_value]
  have hd := congrArg (fun f => H.iCycles 0 (e0.hom (f (intervalTruncEdge A H w))))
    (H.truncLE'_d_eq_toCycles (ComplexShape.embeddingUpIntLE 0)
      (i := 1) (j := 0) (i' := -1) (j' := 0) rfl (by simp) (by simp)
      ((ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).mpr rfl))
  simp only [ModuleCat.comp_apply] at hd
  dsimp only [intervalTruncEdge] at hd
  erw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hd
  have hc := ConcreteCategory.congr_hom (H.toCycles_i (-1) 0) w
  change H.iCycles 0 (H.toCycles (-1) 0 w) = H.d (-1) 0 w at hc
  exact hd.trans (hc.trans hw)
/-- 閉零次値とその境界の式から作った、元の正規化区間の写像。 -/
def normalizedIntervalCochainMapOfBoundary
    (x y : H.X 0) (hx : H.d 0 1 x = 0) (hy : H.d 0 1 y = 0)
    (w : H.X (-1)) (hw : H.d (-1) 0 w = y - x) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ⟶ H :=
  normalizedIntervalCochainMap A H (intervalTruncCycle A H x hx) (intervalTruncCycle A H y hy)
    (intervalTruncEdge A H w) (intervalTrunc_boundary A H x y hx hy w hw)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
