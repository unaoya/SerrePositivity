module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarSplittingCoefficients

/-!
概要：元の coherent 図式の内部次元層を、非退化ホモロジー bar の係数へ同定する。
方針：次元を固定したラベルを再添字付けし、始点のホモロジー同型を使う。
規約：全整数次数と全次元を扱い、strict な持上げを選ばない。
使われ方：単体次元フィルトレーションの一次微分の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

def dgCoherentBarLayerIndexEquiv (I : SSet.{u}) (n : ℕ) :
    I.nonDegenerate n ≃ dgCoherentBarLayerIndex I n where
  toFun s := ⟨⟨⟨n, s.val⟩, s.property⟩, rfl⟩
  invFun s := by
    rcases s with ⟨⟨⟨m, t⟩, ht⟩, h⟩
    change m = n at h
    subst m
    exact ⟨t, ht⟩
  left_inv s := rfl
  right_inv s := by
    rcases s with ⟨⟨⟨m, t⟩, ht⟩, h⟩
    change m = n at h
    subst m
    rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarSource_nerve (n : ℕ) (s : (nerve J) _⦋n⦌) :
    dgCoherentBarSource R D G ⟨n, s⟩ =
      coherentDiagramVertex G (nerveEquiv.symm (s.obj 0)) := by
  unfold dgCoherentBarSource
  congr 1

def dgCoherentBarLayerCoefficientIso (x : D) (q : ℤ) (n : ℕ)
    (s : (nerve J).nonDegenerate n) :
    ((dgCoherentBarSource R D G ⟨n, s.val⟩).obj (Opposite.op x)).homology ((n : ℤ) + q) ≅
      dgHomologyBarNondegFamily R (dgCoherentBarHomologyDiagram R D G x ((n : ℤ) + q)) n s := by
  rw [dgCoherentBarSource_nerve]
  exact (dgCoherentBarHomologyDiagramObjIso R D G x ((n : ℤ) + q) (s.val.obj 0)).symm

def dgCoherentBarLayerHomologyCoefficientsIso (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)).homology q ≅
      dgHomologyBarNondegGraded R (dgCoherentBarHomologyDiagram R D G x ((n : ℤ) + q)) n :=
  dgCoherentBarLayerHomologyIso R D G x q n ≪≫
    (Sigma.reindex (dgCoherentBarLayerIndexEquiv (nerve J) n)
      (fun s => ((dgCoherentBarSource R D G s.val.val).obj
        (Opposite.op x)).homology ((n : ℤ) + q))).symm ≪≫
    Sigma.mapIso (fun s => by
      change ((dgCoherentBarSource R D G ⟨n, s.val⟩).obj
        (Opposite.op x)).homology ((n : ℤ) + q) ≅ _
      exact dgCoherentBarLayerCoefficientIso R D G x q n s)

end SerrePositivity.InfinityCategories
