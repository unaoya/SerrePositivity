module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ModulePiTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModulePiMooreNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModulePiZeroMoore
/-!
概要：単体的加群の全基点の正次数 π を Moore ホモロジーへ自然に同定する。
方針：加法平行移動の逆と零基点の Moore 比較を合成する。
規約：次数は n+1。任意指定道による移送は同じホモロジー元で検出する。
使われ方：評価ホモロジー余錐から橋の各元ごとの条件を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory AlgebraicTopology Opposite SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]
  (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)]

/-- 全基点での π_{n+1} と、同じ正規化 Moore 複体の H_{n+1}。 -/
def dgBarCompactModulePiHomologyEquiv (n : ℕ) (x : W.obj (op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x ≃*
      Multiplicative (((normalizedMooreComplex (ModuleCat.{v} R)).obj W).homology (n + 1)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)).symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv W n)

variable {W} {V : SimplicialObject (ModuleCat.{v} R)} [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]

lemma dgBarCompactModulePiHomologyEquiv_naturality
    (f : W ⟶ V) (n : ℕ) (x : W.obj (op ⦋0⦌))
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x) :
    dgBarCompactModulePiHomologyEquiv V n ((f.app (op ⦋0⦌)).hom x)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiMap n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) x a) =
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} R)).map f)
        (n + 1)).hom (dgBarCompactModulePiHomologyEquiv W n x a) := by
  obtain ⟨a₀, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)).surjective a
  change dgBarCompactModulePiHomologyEquiv V n _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) rfl _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_pi_naturality]
  simp only [dgBarCompactModulePiHomologyEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv V n)
    (e.symm (e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) a₀))) = _
  rw [MulEquiv.symm_apply_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv_naturality f n a₀

lemma dgBarCompactModulePiTransport_of_homology_eq (n : ℕ)
    {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n x)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n y)
    (h : dgBarCompactModulePiHomologyEquiv W n x a =
      dgBarCompactModulePiHomologyEquiv W n y b) : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e a b := by
  let ex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)
  let ey := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W y)
  have h₀ : ex.symm a = ey.symm b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiMooreGroupEquiv W n).injective h
  have hb : ey (ex.symm a) = b := by
    apply ey.symm.injective
    simpa only [MulEquiv.symm_apply_apply] using h₀
  rw [← hb]
  have ht := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiTransport W n e (ex.symm a)
  change _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e (ex (ex.symm a)) (ey (ex.symm a)) at ht
  rw [MulEquiv.apply_symm_apply] at ht
  exact ht

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
