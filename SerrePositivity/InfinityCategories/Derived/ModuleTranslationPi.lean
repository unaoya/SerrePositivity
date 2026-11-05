module
public import SerrePositivity.InfinityCategories.Derived.ModuleTranslation
public import SerrePositivity.InfinityCategories.Kan.HomotopyIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleTranslationIso_pi_naturality
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (x : W.obj (op ⦋0⦌)) (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet W) n 0) :
    _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f) rfl
      (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso n (moduleTranslationIso W x)
        (moduleTranslationIso_zero W x) s) =
    _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso n
      (moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
      (moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
      (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
        (moduleUnderlyingSSetMap_zero f) s) := by
  let y := (f.app (op ⦋0⦌)).hom x
  have h₁ : ((moduleTranslationIso W x).hom ≫ moduleUnderlyingSSetMap f).app _ 0 = y := by
    change (moduleUnderlyingSSetMap f).app _ ((moduleTranslationIso W x).hom.app _ 0) = y
    rw [moduleTranslationIso_zero]
    rfl
  have h₂ : (moduleUnderlyingSSetMap f ≫ (moduleTranslationIso V y).hom).app _ 0 = y := by
    change (moduleTranslationIso V y).hom.app _ ((moduleUnderlyingSSetMap f).app _ 0) = y
    rw [moduleUnderlyingSSetMap_zero, moduleTranslationIso_zero]
  have h := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_comp (n := n) (x := (0 : W.obj (op ⦋0⦌)))
    (moduleTranslationIso W x).hom (moduleTranslationIso_zero W x)
    (moduleUnderlyingSSetMap f) rfl h₁
  simp only [moduleTranslationIso_naturality] at h
  have h' := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_comp (n := n) (x := (0 : W.obj (op ⦋0⦌)))
    (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f)
    (moduleTranslationIso V y).hom (moduleTranslationIso_zero V y) h₂
  exact (DFunLike.congr_fun h s).symm.trans (DFunLike.congr_fun h' s)
lemma modulePiMap_bijective_at_iff_zero
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (x : W.obj (op ⦋0⦌)) (n : ℕ) :
    Function.Bijective
      (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (x := x) (moduleUnderlyingSSetMap f) rfl) ↔
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
      (moduleUnderlyingSSetMap_zero f)) := by
  have h := funext (moduleTranslationIso_pi_naturality f x n)
  let e := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso n (moduleTranslationIso W x)
    (moduleTranslationIso_zero W x)
  let e' := _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.equivOfIso n
    (moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
    (moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
  exact (e.toEquiv.bijective_comp _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective h)).trans (e'.toEquiv.comp_bijective _))
end SerrePositivity.InfinityCategories
