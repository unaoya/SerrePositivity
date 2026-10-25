module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerConnecting

/-!
概要：実フィルトレーションの一次ホモロジー複体と非退化 H(G) bar の同型。
方針：実連結射と一次層作用素の比較を、総次数を固定した層同型へ合わせる。
規約：元の coherent 図式の高次成分を保持した実フィルトレーションを使う。
使われ方：全正単体次元の完全性と有限 support による収束。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet HomologicalComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarConnectingHomology_comparison (x : D) (n : ℕ) (p t r : ℤ)
    (hpt : p + 1 = t) (hs : ((n + 1 : ℕ) : ℤ) + p = r) (ht : (n : ℤ) + t = r) :
    ((dgCoherentBarLayerSequence_shortExact R D G x n).δ p t
        (by change p + 1 = t; exact hpt) ≫
      HomologicalComplex.homologyMap (dgCoherentBarStageToLayer R D G x n) t) ≫
        (dgCoherentBarNaturalLayerHomologyIso R D G x n t r ht).hom =
    (dgCoherentBarNaturalLayerHomologyIso R D G x (n + 1) p r hs).hom ≫
      (dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x r)).d (n + 1) n := by
  subst t
  erw [dgCoherentBarLayerConnecting_eq_firstHomology]
  have hr : p + ((n : ℤ) + 1) = r := by omega
  obtain rfl : r = p + ((n : ℤ) + 1) := hr.symm
  exact dgCoherentBarFirstLayerHomology_differential R D G x p n

def dgCoherentBarFirstHomologyComparison (x : D) (r : ℤ) :
    dgCoherentBarFirstHomologyComplex R D G x r ≅
      dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x r) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => dgCoherentBarNaturalLayerHomologyIso R D G x n (r - (n : ℤ)) r (by omega))
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      dsimp only [dgCoherentBarFirstHomologyComplex]
      rw [ChainComplex.of_d]
      symm
      dsimp only [dgCoherentBarFirstHomologyDifferential]
      exact dgCoherentBarConnectingHomology_comparison R D G x j
        (r - ((j + 1 : ℕ) : ℤ)) (r - (j : ℤ)) r (by omega) (by omega) (by omega))

lemma dgCoherentBarFirstHomology_exactAt [IsFiltered J] (x : D) (r : ℤ) (n : ℕ) :
    (dgCoherentBarFirstHomologyComplex R D G x r).ExactAt (n + 1) := by
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (dgHomologyBarNondeg_exactAt R (dgCoherentBarHomologyDiagram R D G x r) n)
  exact h.of_iso (HomologicalComplex.homologyMapIso (dgCoherentBarFirstHomologyComparison R D G x r) (n + 1))

def dgCoherentBarFirstHomologyZeroIso (x : D) (r : ℤ) :
    (dgCoherentBarFirstHomologyComplex R D G x r).homology 0 ≅
      colimit (dgCoherentBarHomologyDiagram R D G x r) :=
  HomologicalComplex.homologyMapIso (dgCoherentBarFirstHomologyComparison R D G x r) 0 ≪≫
    dgHomologyBarNondegZeroHomologyIso R (dgCoherentBarHomologyDiagram R D G x r)

end SerrePositivity.InfinityCategories
