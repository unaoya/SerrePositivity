module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ClosedCompositionCochain
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Basic
/-! 挿入した比較 cochain を全次数の加群 Hom 後合成へ移し、Yoneda の全次数での自然性を示す。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (T U V : RightModule R C) {K : Complex R} (i : 𝟙_ (Complex R) ⟶ K)
  (p : ℤ) (h : Cochain K (moduleHom R C U V) p)

lemma dgGluingModulePostAction :
    (Cochain.ofHom ((ρ_ (moduleHom R C T U)).inv ≫ (moduleHom R C T U) ◁ i)).comp
      (((tensorLeftHom (moduleHom R C T U) K (moduleHom R C U V)).f p h).comp
        (Cochain.ofHom (moduleComposition R C T U V)) (add_zero p)) (zero_add p) =
    (modulePostcompositionMap R C T U V).f p
      (h.v 0 p (zero_add p) (cycleFromUnit K i).val) := by
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply,
    HomologicalComplex.comp_f, ModuleCat.comp_apply, complexRightUnitor_inv_apply,
    SerrePositivity.DifferentialGraded.whiskerLeft_apply,
    tensorLeftHom_apply_of_sum (moduleHom R C T U) K
      (moduleHom R C U V) p q 0 q p n (add_zero q) (zero_add p) hn,
    modulePostcompositionMap_apply]
  simp only [Units.smul_def, map_zsmul, compose, mul_comm p q]
  rfl

lemma dgGluingYonedaPostAction (c : C) (z : (moduleHom R C U V).X p) :
    ((modulePostcompositionMap R C (representable R c) U V).f p z).comp
      (Cochain.ofHom (dgYonedaIso R c V).hom) (add_zero p) =
    (Cochain.ofHom (dgYonedaIso R c U).hom).comp
      ((moduleHomπ R C U V c).f p z) (zero_add p) := by
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  rw [cochain_comp_ofHom_apply, cochain_ofHom_comp_apply]
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply,
    modulePostcompositionMap_apply, moduleHomCompose_π]
  rw [Cochain.comp_v _ _ hn 0 q n (zero_add q) hn]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
