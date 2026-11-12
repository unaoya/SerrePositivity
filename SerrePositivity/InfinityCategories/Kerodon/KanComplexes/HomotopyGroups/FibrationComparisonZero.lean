module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponentNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares

/-!
概要：Kan fibration の可換正方形の全空間・底の π_* 同型から fiber の連結成分の全単射。
方針：fiber 内の参照頂点を選び直し、零次数の完全性と基本群の全単射性を使う。
規約：正次数の群の五項補題から零次数の結論を推論しない。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。fiber の全次数の比較。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra.FibrationSquare

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：全空間と底が全基点 π_* 同型の可換正方形は fiber の連結成分で全単射。
方針：単射性では参照頂点を原像の頂点へ移し、全射性では全空間の成分を先に持ち上げる。
規約：源の fiber は指定した全空間の頂点 e₀ の像の上に取る。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）。零次数の fiber の比較。 -/
theorem fiberMap_piZero_bijective {E B E' B' : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex E'] [KanComplex B']
    (p : E ⟶ B) (p' : E' ⟶ B') [Fibration p] [Fibration p']
    (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) (e₀ : E _⦋0⦌) :
    Function.Bijective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e₀)) := by
  let b := p.app _ e₀
  let b' := p'.app _ (f.app _ e₀)
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b
  let ι' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' b'
  let φ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e₀
  have hφ : φ ≫ ι' = ι ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e₀
  have hπ : ∀ a, mapπ₀ f (mapπ₀ ι a) = mapπ₀ ι' (mapπ₀ φ a) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square ι ι' φ f hφ.symm
  have hf₀ := hf.piZero_bijective_at e₀
  have hg₀ := hg.piZero_bijective_at (p.app _ e₀)
  constructor
  · intro a c hac
    obtain ⟨v, rfl⟩ := π₀.mk_surjective a
    let e := ι.app _ v
    have hb : p.app _ e = b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base p b v
    have hb' : p'.app _ (f.app _ e) = b' :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e).symm.trans
        ((congrArg (g.app _) hb).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e₀))
    have hφv : ι'.app _ (φ.app _ v) = f.app _ e :=
      congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b ⟶ E' ↦ k.app _ v) hφ
    have hE : mapπ₀ ι c = π₀.mk e := by
      apply hf₀.injective
      rw [hπ c, ← hac, ← hπ (π₀.mk v), mapπ₀_mk]
    obtain ⟨β, hβ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact p e b hb c).1 hE
    have hnat := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_natural p p' f g comm e b hb b' hb' φ hφ β
    have hker' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p' (f.app _ e) b' hb'
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) β) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p' (f.app _ e) b' hb' 1 := by
      calc
        _ = mapπ₀ φ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p e b hb β) := hnat.symm
        _ = mapπ₀ φ c := congrArg (mapπ₀ φ) hβ
        _ = mapπ₀ φ (π₀.mk v) := hac.symm
        _ = π₀.mk (φ.app _ v) := mapπ₀_mk φ v
        _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_one_at p' (f.app _ e) b' hb' (φ.app _ v) hφv).symm
    obtain ⟨α', hα'⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_kernel p' (f.app _ e) b' hb' _).1 hker'
    obtain ⟨α, hα⟩ :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism 0 f hf (x := e) rfl).surjective α'
    have hpα : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl α = β := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism 0 g hg
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e)).injective
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square p p' f g comm rfl rfl rfl
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) 0 α, hα, hα']
    have hker := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_kernel p e b hb β).2 ⟨α, hpα⟩
    exact (hβ.symm.trans (hker.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_one_at p e b hb v rfl))).symm
  · intro a'
    obtain ⟨aE, haE⟩ := hf₀.surjective (mapπ₀ ι' a')
    have hpE : mapπ₀ p aE = π₀.mk b := by
      apply hg₀.injective
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square p p' f g comm aE, haE]
      have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentFiber_exact p' (f.app _ e₀) (mapπ₀ ι' a')).2 ⟨a', rfl⟩
      exact ht.trans ((mapπ₀_mk g b).trans (congrArg π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e₀))).symm
    obtain ⟨s, hs⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentFiber_exact p e₀ aE).1 hpE
    obtain ⟨v, rfl⟩ := π₀.mk_surjective s
    let e := ι.app _ v
    have hb : p.app _ e = b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_base p b v
    have hb' : p'.app _ (f.app _ e) = b' :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e).symm.trans
        ((congrArg (g.app _) hb).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e₀))
    have hE' : mapπ₀ ι' a' = π₀.mk (f.app _ e) := by
      calc
        _ = mapπ₀ f aE := haE.symm
        _ = mapπ₀ f (mapπ₀ ι (π₀.mk v)) := congrArg (mapπ₀ f) hs.symm
        _ = _ := by rw [mapπ₀_mk, mapπ₀_mk]
    obtain ⟨β', hβ'⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_exact p' (f.app _ e) b' hb' a').1 hE'
    obtain ⟨β, hβ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism 0 g hg
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e)).surjective β'
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p e b hb β, ?_⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting_natural p p' f g comm e b hb b' hb' φ hφ β).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.componentConnecting p' (f.app _ e) b' hb') hβ).trans hβ')

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap_piZero_bijective := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberMap_piZero_bijective
