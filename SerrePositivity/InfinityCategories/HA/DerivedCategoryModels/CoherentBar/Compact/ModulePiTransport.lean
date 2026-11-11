module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PiTransportMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModuleTranslationPi
/-!
概要：単体的加群の正次数 π の基点移送は、全ての指定道で同じ平行移動になる。
方針：零基点の球面に区間の道を加える実円柱を構成する。
規約：道を選び直さず、球面境界上で指定道に厳密に一致する。
使われ方：評価ホモロジーから橋の全基点・全指定道条件を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Opposite SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] (W : SimplicialObject (ModuleCat.{v} R))

def dgBarCompactModuleAddMaps {K : SSet.{v}}
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W where
  app n := ↾fun s => f.app n s + g.app n s
  naturality {n m} α := by
    ext s
    symm
    change (W.map α).hom (f.app n s + g.app n s) = _
    rw [map_add]
    exact congrArg₂ (· + ·)
      (ConcreteCategory.congr_hom (f.naturality α) s).symm
      (ConcreteCategory.congr_hom (g.naturality α) s).symm

private lemma dgBarCompactModuleEdge_zero {K : SSet.{v}}
    {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) :
    (SSet.const (stdSimplex.obj₀Equiv.symm 0) : K ⟶ Δ[1]) ≫
      SSet.yonedaEquiv.symm e.edge = SSet.const x := by
  rw [SSet.const_comp]
  congr 1
  have h : SSet.yonedaEquiv (stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm e.edge) = x := by
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact e.src_eq
  simpa only [stdSimplex.δ_one_eq_const, SSet.const_comp, SSet.yonedaEquiv_const] using h

private lemma dgBarCompactModuleEdge_one {K : SSet.{v}}
    {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) :
    (SSet.const (stdSimplex.obj₀Equiv.symm 1) : K ⟶ Δ[1]) ≫
      SSet.yonedaEquiv.symm e.edge = SSet.const y := by
  rw [SSet.const_comp]
  congr 1
  have h : SSet.yonedaEquiv (stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm e.edge) = y := by
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact e.tgt_eq
  simpa only [stdSimplex.δ_zero_eq_const, SSet.const_comp, SSet.yonedaEquiv_const] using h

def dgBarCompactModulePathHomotopy {K : SSet.{v}}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) {x y : W.obj (op ⦋0⦌)}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) :
    SSet.Homotopy (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x).hom)
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W y).hom) where
  h := dgBarCompactModuleAddMaps W (fst K Δ[1] ≫ f)
    (snd K Δ[1] ≫ SSet.yonedaEquiv.symm e.edge)
  h₀ := by
    ext n s
    have h := congrArg (fun q : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W => q.app n s)
      (dgBarCompactModuleEdge_zero W (K := K) e)
    change f.app n s + _ = f.app n s + _
    exact congrArg (f.app n s + ·) h
  h₁ := by
    ext n s
    have h := congrArg (fun q : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W => q.app n s)
      (dgBarCompactModuleEdge_one W (K := K) e)
    change f.app n s + _ = f.app n s + _
    exact congrArg (f.app n s + ·) h
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

lemma dgBarCompactModulePathHomotopy_boundary (n : ℕ)
    (f : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).PtSimplex (n + 1) 0)
    {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) :
    ((SSet.boundary (n + 1)).ι ▷ Δ[1]) ≫
      (dgBarCompactModulePathHomotopy W f.map e).h =
      snd _ _ ≫ SSet.yonedaEquiv.symm e.edge := by
  have hz : (SSet.boundary (n + 1)).ι ≫ f.map = SSet.const (0 : W.obj (op ⦋0⦌)) := by
    simpa only [Subcomplex.ofSimplex_ι, SSet.comp_const] using f.comm
  ext m s
  have h := congrArg (fun q : (SSet.boundary (n + 1)).toSSet ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W => q.app m s.1) hz
  change f.map.app m ((SSet.boundary (n + 1)).ι.app m s.1) =
    (W.map (m.unop.const ⦋0⦌ 0).op).hom 0 at h
  rw [map_zero] at h
  change f.map.app m ((SSet.boundary (n + 1)).ι.app m s.1) + _ = _
  rw [h, zero_add]
  rfl

lemma dgBarCompactModulePiTransport [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)]
    (n : ℕ) {x y : W.obj (op ⦋0⦌)} (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiTransport n e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x) a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W y) a) := by
  induction a using Quotient.inductionOn with
  | h f =>
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x) f,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W y) f, rfl, rfl,
      dgBarCompactModulePathHomotopy W f.map e, ?_⟩
    exact dgBarCompactModulePathHomotopy_boundary W n f e

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
