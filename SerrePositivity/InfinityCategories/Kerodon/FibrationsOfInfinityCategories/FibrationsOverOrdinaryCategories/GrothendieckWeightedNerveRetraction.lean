module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveForward
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNerveInverseFunctor

/-!
概要：元のGrothendieck射列の係数から、同じ対象と射列を回収する。
方針：Yonedaの往復とprefixの最終対象・最終射の評価を使う。
規約：IS-W2 R03eの左往復。元の射列の対象を変えない。
使われ方：厳密なweighted nerve比較の単射性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

/-- 元の射列の係数のYoneda表示は、元の同じprefixである。 -/
theorem grothWeightedNerveFiberChain_forward (i : Fin (n+1)) :
    grothWeightedNerveFiberChain F (grothWeightedNerveSimplex F σ) i =
      grothWeightedPrefixFiber F σ i := by
  exact (SSet.yonedaEquiv (X := nerve (F.obj (σ.obj i).base))
    (n := SimplexCategory.mk i.val)).apply_symm_apply _

/-- 元の射列の係数から回収した対象は、元の同じ対象である。 -/
theorem grothWeightedNerveInverseObj_forward (i : Fin (n+1)) :
    grothWeightedNerveInverseObj F (grothWeightedNerveSimplex F σ) i = σ.obj i := by
  change (⟨(σ.obj i).base, (grothWeightedNerveFiberChain F
    (grothWeightedNerveSimplex F σ) i).obj (Fin.last i.val)⟩ : Grothendieck F) = _
  rw [grothWeightedNerveFiberChain_forward, grothWeightedPrefixFiber_last]

/-- 元の射列の同じprefixの最終射は、元のfiber射に一致する。 -/
theorem grothWeightedPrefixFiber_last_map {i j : Fin (n+1)} (f : i ⟶ j) :
    (grothWeightedPrefixFiber F σ j).map (homOfLE
      (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from leOfHom f)) =
        eqToHom (by
          rw [grothWeightedPrefixFiber_obj]
          rfl) ≫ (σ.map f).fiber ≫
            eqToHom (grothWeightedPrefixFiber_last F σ j).symm := by
  simp only [grothWeightedPrefixFiber, Functor.comp_map,
    SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transport,
    grothWeightedPrefixArrow, CostructuredArrow.homMk_left,
    CostructuredArrow.mk_hom_eq_self]
  change eqToHom _ ≫ (F.map (σ.map (𝟙 j)).base).toFunctor.map (σ.map f).fiber =
    eqToHom _ ≫ (σ.map f).fiber ≫ eqToHom _
  have hh : (F.map (σ.map (𝟙 j)).base).toFunctor = 𝟭 (F.obj (σ.obj j).base) := by
    rw [σ.map_id, Grothendieck.id_base, F.map_id]
    rfl
  rw [CategoryTheory.Functor.congr_hom hh (σ.map f).fiber]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc]

/-- 元のGrothendieck射列を係数から回収すると、同じ全射列に戻る。 -/
theorem grothWeightedNerveInverseSimplex_forward :
    grothWeightedNerveInverseSimplex F (grothWeightedNerveSimplex F σ) = σ := by
  refine CategoryTheory.Functor.ext (grothWeightedNerveInverseObj_forward F σ) ?_
  intro i j f
  apply Grothendieck.ext _ _ (by
    simp only [Grothendieck.comp_base, Grothendieck.base_eqToHom,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl)
  simp only [Grothendieck.comp_fiber, Grothendieck.fiber_eqToHom,
    Grothendieck.base_eqToHom, eqToHom_refl, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans_assoc]
  simp only [grothWeightedNerveInverseSimplex, grothWeightedNerveInverseMap,
    grothWeightedNerveFiberChain_forward, Grothendieck.base_eqToHom, eqToHom_refl]
  rw [CategoryTheory.Functor.congr_hom (grothWeightedNerveFiberChain_forward F σ j)
    (homOfLE (show grothWeightedNerveInverseIndex f ≤ Fin.last j.val from leOfHom f))]
  simp only [eqToHom_trans_assoc]
  have hh : (F.map (eqToHom (grothWeightedNerveInverseObj_forward F σ j).symm).base).toFunctor =
      𝟭 (F.obj (σ.obj j).base) := by
    rw [Grothendieck.base_eqToHom]
    change (F.map (𝟙 (σ.obj j).base)).toFunctor = _
    rw [F.map_id]
    rfl
  rw [CategoryTheory.Functor.congr_hom hh (σ.map f).fiber]
  simp only [Functor.id_map, Category.assoc, eqToHom_trans_assoc]
  rw [grothWeightedPrefixFiber_last_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
