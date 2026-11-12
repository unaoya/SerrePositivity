module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiHomology
/-!
概要：単体的加群の零基点チャートを全基点へ延長する。
方針：全基点 Moore 比較を零基点の逆比較と合成する。
規約：任意指定道による移送を同じチャート値で検出する。
使われ方：反転・宇宙持ち上げの線形模型から native 評価へチャートを渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology Opposite SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]
  {W V : SimplicialObject (ModuleCat.{v} R)}
  [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
  {A B : Type w}

/-- 零基点のチャートから同じ加群の全基点への延長。 -/
def dgBarCompactModuleZeroChartExtension (n : ℕ)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃ A)
    (x : W.obj (op ⦋0⦌)) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x ≃ A :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)).symm.toEquiv.trans e

lemma dgBarCompactModuleZeroChartExtension_transport (n : ℕ)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃ A)
    {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n y)
    (h : dgBarCompactModuleZeroChartExtension n α x a =
      dgBarCompactModuleZeroChartExtension n α y b) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiTransport_of_homology_eq n e a b
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv W n) (α.injective h)

lemma dgBarCompactModuleZeroChartExtension_naturality (f : W ⟶ V) (n : ℕ)
    (α : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃ A)
    (β : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V) n 0 ≃ B) (g : A → B)
    (h : ∀ a, β (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) a) = g (α a))
    (x : W.obj (op ⦋0⦌)) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x) :
    dgBarCompactModuleZeroChartExtension n β ((f.app _).hom x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) x a) =
      g (dgBarCompactModuleZeroChartExtension n α x a) := by
  let ex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)
  obtain ⟨a₀, rfl⟩ := ex.surjective a
  change dgBarCompactModuleZeroChartExtension n β _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) rfl _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_pi_naturality]
  have he (U : SimplicialObject (ModuleCat.{v} R))
      [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet U)]
      (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet U) n 0 ≃ B)
      (z : U.obj (op ⦋0⦌)) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet U) n 0) :
      dgBarCompactModuleZeroChartExtension n e₀ z
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso U z)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero U z) b) = e₀ b := by
    simp only [dgBarCompactModuleZeroChartExtension, Equiv.trans_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply]
  change dgBarCompactModuleZeroChartExtension n β ((f.app _).hom x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V ((f.app _).hom x))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero V ((f.app _).hom x)) _) = _
  rw [he]
  have hW : dgBarCompactModuleZeroChartExtension n α x (ex a₀) = α a₀ := by
    simp only [dgBarCompactModuleZeroChartExtension, Equiv.trans_apply,
      MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply, ex]
  rw [hW]
  exact h a₀

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
