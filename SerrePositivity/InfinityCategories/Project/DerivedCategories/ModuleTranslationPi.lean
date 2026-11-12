module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ModuleTranslation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso
/-!
概要：実加法同型による正次数 π の全基点への移送。
方針：元の射と全基点の誘導写像を保ち、既存の実 Whitehead 逆へ接続する。
規約：可換性・平坦性を仮定しない。使われ方：β5(g) の正規化界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleTranslationIso_pi_naturality
    [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) (x : W.obj (op ⦋0⦌)) (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x) s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f) s) := by
  let y := (f.app (op ⦋0⦌)).hom x
  have h₁ : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f).app _ 0 = y := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f).app _ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x).hom.app _ 0) = y
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero]
    rfl
  have h₂ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V y).hom).app _ 0 = y := by
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V y).hom.app _ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f).app _ 0) = y
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) (x := (0 : W.obj (op ⦋0⦌)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) rfl h₁
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_naturality] at h
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) (x := (0 : W.obj (op ⦋0⦌)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V y).hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero V y) h₂
  exact (DFunLike.congr_fun h s).symm.trans (DFunLike.congr_fun h' s)
lemma modulePiMap_bijective_at_iff_zero
    [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet V)]
    (f : W ⟶ V) (x : W.obj (op ⦋0⦌)) (n : ℕ) :
    Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (x := x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) rfl) ↔
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap_zero f)) := by
  have h := funext (moduleTranslationIso_pi_naturality f x n)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso W x)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero W x)
  let e' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
  exact (e.toEquiv.bijective_comp _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective h)).trans (e'.toEquiv.comp_bijective _))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
