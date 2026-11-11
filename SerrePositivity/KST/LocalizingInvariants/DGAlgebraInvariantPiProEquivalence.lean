module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovQuotientSuccessorValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteMapValuePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantQuasiIso

/-!
概要：k-connective 不変量の元の実値は、代数の全整数 π-pro 同値を π-pro 同値へ送る。
方針：値の必要次数に応じて有限切断を選び、実有限逆と商射の群同型の正方形で比較する。
規約：連結なレベル表示や不変量の連続性を追加入力にしない。
使われ方：連結な実レベル表示の比較脚と LT Cor. 2.31 の弱同値の帰結。
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

lemma postnikovQuotientLevelHom_square (cutoff : ℤ) :
    (f.map (nonpositiveInclusion R)).comp (postnikovQuotientLevelHom R B cutoff) =
      (postnikovQuotientLevelHom R A cutoff).comp (f.map (postnikovFunctor R cutoff)) := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact (postnikovQuotient_naturality R (f.app i).hom cutoff).symm

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (h : IsKConnective R Φ k)
include h

lemma IsKConnective.invariantLevelMap_piProEquivalence_of_piProEquivalence
    (hpi : IsPiProEquivalence R (f.map (nonpositiveInclusion R))) :
    ProSpectrum.IsPiProEquivalence (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) := by
  intro j
  let cutoff : ℤ := max 0 (j - k)
  have hc : 0 ≤ cutoff := le_max_left _ _
  have hj : j < cutoff + 1 + k := by have := le_max_right 0 (j - k); omega
  let L := invariantFunctor R Φ
  let P := SpectrumHo.piFunctor j
  let a := ((postnikovQuotientLevelHom R A cutoff).map L).map P
  let b := ((postnikovQuotientLevelHom R B cutoff).map L).map P
  have : ∀ i, IsIso (a.app i) := by
    intro i
    have : (A.obj i).obj.X.IsStrictlyLE 0 := (A.obj i).property
    exact h.postnikovQuotient_pi_isIso R Φ (A.obj i).obj cutoff hc j hj
  have : ∀ i, IsIso (b.app i) := by
    intro i
    have : (B.obj i).obj.X.IsStrictlyLE 0 := (B.obj i).property
    exact h.postnikovQuotient_pi_isIso R Φ (B.obj i).obj cutoff hc j hj
  have hcut := (postnikovFiniteMap_isProIso_of_connective R cutoff hc f L
    (fun z _ _ => hpi z) (h.invariantFunctor_invertsConnectiveQuasiIsos R Φ)).map P
  change IsProIso (((f.map (nonpositiveInclusion R)).map L).map P)
  apply TowerDiagram.proIso_of_square_reverse (((f.map (nonpositiveInclusion R)).map L).map P)
    (((f.map (postnikovFunctor R cutoff)).map L).map P) a b
  · have hs := congrArg (fun t => (t.map L).map P) (postnikovQuotientLevelHom_square R f cutoff)
    simpa only [TowerDiagram.levelHom_map_comp] using hs
  · exact hcut

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
