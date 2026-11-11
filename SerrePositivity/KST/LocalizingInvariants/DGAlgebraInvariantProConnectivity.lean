module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantPiProEquivalence
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectedLevelRepresentation
public import SerrePositivity.KST.LocalizingInvariants.ProGroupConnectedComposition

/-!
概要：元の代数の n-pro 連結射を、元の不変量値の (n+k)-pro 連結射へ送る。
方針：構成済みの連結な実レベル表示に k-connective 条件を適用し、比較脚の像で移す。
規約：n≥1。レベル表示やその値の同値性を追加入力にしない。
使われ方：LT Cor. 2.31 の元の dg 代数と実 Perf 値への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
include h

lemma IsKConnective.invariantLevelMap_piProConnected (n : ℤ) (hn : 1 ≤ n)
    (hf : IsPiProConnected R (f.map (nonpositiveInclusion R)) n) :
    ProSpectrum.IsPiProConnected (invariantLevelMap R Φ (f.map (nonpositiveInclusion R)))
      (n + k) := by
  let c := connectedLevelRepresentation R f n hn hf
  let L := invariantFunctor R Φ
  have hright := h.invariantLevelMap_piProEquivalence_of_piProEquivalence R c.right Φ
    c.right_piProEquivalence
  have hv (i : ℕ) :
      (∀ j : ℤ, j < n + k →
        Function.Injective (invariantGroupMap R Φ (c.left.app i).hom j)) ∧
      ∀ j : ℤ, j ≤ n + k →
        Function.Surjective (invariantGroupMap R Φ (c.left.app i).hom j) := by
    have : (A.obj i).obj.X.IsStrictlyLE 0 := (A.obj i).property
    have : (c.middle.obj i).obj.X.IsStrictlyLE 0 := (c.middle.obj i).property
    exact h.2 (nonpositive_isConnective R (A.obj i).obj)
      (nonpositive_isConnective R (c.middle.obj i).obj) (c.left.app i).hom n hn
      ⟨(c.left_connected i).1 0 (by omega), (c.left_connected i).2 0 (by omega)⟩
      (c.left_connected i)
  constructor
  · intro j hj
    let P := SpectrumHo.piFunctor j
    let fl := ((c.left.map (nonpositiveInclusion R)).map L).map P
    let gr := ((c.right.map (nonpositiveInclusion R)).map L).map P
    have hi : ∀ i, Function.Injective (fl.app i).hom := fun i =>
      SpectrumHo.piFunctor_map_injective_of_native (invariantMap R Φ (c.left.app i).hom) j
        ((hv i).1 j hj)
    have hh := ProGroup.kernelTrivial_comp_of_injective fl gr hi
      (ProGroup.kernelTrivial_of_proIso (hright j))
    have hs : fl.comp gr = (((f.map (nonpositiveInclusion R)).map L).map P) := by
      simpa only [TowerDiagram.levelHom_map_comp] using
        congrArg (fun t => ((t.map (nonpositiveInclusion R)).map L).map P) c.fac
    rw [hs] at hh
    exact hh
  · intro j hj
    let P := SpectrumHo.piFunctor j
    let fl := ((c.left.map (nonpositiveInclusion R)).map L).map P
    let gr := ((c.right.map (nonpositiveInclusion R)).map L).map P
    have hs : ∀ i, Function.Surjective (fl.app i).hom := fun i =>
      SpectrumHo.piFunctor_map_surjective_of_native (invariantMap R Φ (c.left.app i).hom) j
        ((hv i).2 j hj)
    have hh := ProGroup.imageSurjective_comp_of_surjective fl gr hs
      (ProGroup.imageSurjective_of_proIso (hright j))
    have he : fl.comp gr = (((f.map (nonpositiveInclusion R)).map L).map P) := by
      simpa only [TowerDiagram.levelHom_map_comp] using
        congrArg (fun t => ((t.map (nonpositiveInclusion R)).map L).map P) c.fac
    rw [he] at hh
    exact hh

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
