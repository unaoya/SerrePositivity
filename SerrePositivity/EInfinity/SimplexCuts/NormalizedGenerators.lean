module

public import SerrePositivity.EInfinity.AlexanderWhitney.NormalizedChains

/-!
# 切断公式で使う整数次数の正規化生成元

Berger–Fresse §2.2.6。既存の一般単体集合の正規化生成元を次数 q ↦ −q で読む。
L04 の証明の分割として、非単射な面から来る生成元の消滅をそのまま運ぶ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A]

abbrev chains (S : SSet.{0}) : Complex A := (BarrattEccles.normalizedFunctor A).obj S

def chainsXIso (S : SSet.{0}) (q : ℕ) :
    (chains A S).X (-(q : ℤ)) ≅ (AlexanderWhitney.chains A S).X q :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat rfl

def gen (S : SSet.{0}) (q : ℕ) (x : S _⦋q⦌) : (chains A S).X (-(q : ℤ)) :=
  (chainsXIso A S q).inv (AlexanderWhitney.generator A S q x)

lemma gen_map_of_not_mono (S : SSet.{0}) (q : ℕ) {Δ : SimplexCategory}
    (θ : ⦋q⦌ ⟶ Δ) (hθ : ¬Mono θ) (x : S.obj (Opposite.op Δ)) :
    gen A S q (S.map θ.op x) = 0 := by
  unfold gen
  rw [AlexanderWhitney.generator_map_of_not_mono A S q θ hθ x, map_zero]

/-- L05 の前提計算1：同じ正規化生成元の射に関する自然性。 -/
lemma gen_naturality {S T : SSet.{0}} (f : S ⟶ T) (q : ℕ) (x : S _⦋q⦌) :
    ((BarrattEccles.normalizedFunctor A).map f).f (-(q : ℤ)) (gen A S q x) =
      gen A T q (f.app _ x) := by
  let g := (BarrattEccles.linearization A).map f
  have h := congrArg (fun z => z.f q)
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality g)
  have hv := congrArg (fun z => z (ModuleCat.freeMk (ULift.up x))) h
  change (AlexanderWhitney.normalization A T).f q
      (g.app _ (ModuleCat.freeMk (ULift.up x))) =
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map g).f q
      (AlexanderWhitney.generator A S q x) at hv
  have hg : g.app _ (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (f.app _ x)) := ModuleCat.free_map_apply _ _
  rw [hg] at hv
  change (HomologicalComplex.extendMap
    ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map g)
      ComplexShape.embeddingDownNat).f (-(q : ℤ)) (gen A S q x) = _
  rw [HomologicalComplex.extendMap_f _ _ (i := q) (i' := -(q : ℤ)) rfl]
  change (chainsXIso A T q).toLinearEquiv.symm
      (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).map g).f q
        ((chainsXIso A S q).toLinearEquiv
          ((chainsXIso A S q).toLinearEquiv.symm (AlexanderWhitney.generator A S q x)))) =
    (chainsXIso A T q).toLinearEquiv.symm (AlexanderWhitney.generator A T q (f.app _ x))
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (chainsXIso A T q).toLinearEquiv.symm hv.symm

end SerrePositivity.EInfinity.SimplexCuts
