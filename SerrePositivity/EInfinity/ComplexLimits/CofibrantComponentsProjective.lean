module

public import SerrePositivity.EInfinity.ComplexLimits.CodiskFibrations

/-!
# 実射影 cofibrant 複体の各次数の射影性

概要：元の射影モデルで cofibrant な複体の各成分は射影加群。
方針：任意 module epi を同じ可縮 disk の trivial fibration へ送り、実 lift を評価する。
規約：元の複体の半自由表示や有限性を仮定しない。
使われ方：非有界テンソルと元の frame 境界の cofibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma projectiveCofibrant_component_projective (P : Complex A)
    (hP : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) (n : ℤ) : Projective (P.X n) := by
  constructor
  intro M N a q hq
  let b := (codiskHomEquiv P N n).symm a
  have hp : (projectiveGeneratingCofibrations A).rlp ((codiskFunctor A n).map q) := by
    rw [projectiveGeneratingCofibrations_rlp]
    exact ⟨codiskFunctor_map_fibration A n q, codiskFunctor_map_quasiIso A n q⟩
  let sq : CommSq (0 : (HomologicalComplex.zero : Complex A) ⟶ codisk M n)
      0 ((codiskFunctor A n).map q) b := ⟨by simp⟩
  obtain ⟨l⟩ := ((hP _ hp).sq_hasLift sq).exists_lift
  refine ⟨codiskHomEquiv P M n l.l, ?_⟩
  rw [← codiskFunctor_map_homEquiv, l.fac_right]
  exact (codiskHomEquiv P N n).apply_symm_apply a

end SerrePositivity.EInfinity.ComplexLimits
