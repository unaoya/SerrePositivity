module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTargetSchur
public import SerrePositivity.EInfinity.BarrattEccles.Theory.InducedCoinvariantTotal

/-!
# Schur の軌道直和から指定二色係数比較への接続

HA 3.2.4.7 の自由比較で、元の入力包含から作った誘導表示と、二色部分群上の
指定係数比較を接続する。群変更は元の商の生成元を保つものを使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

/-- 両方の作用を同じ群同型で制限した全複体の、指定商を保つ比較。 -/
def coinvariantTotalGroupChangeIso {A G H : Type u} [CommRing A] [Group G] [Group H]
    {K L : Complex A} (e : G ≃* H) (ρ : H →* End K) (σ : H →* End L) :
    coinvariantTensorTotal (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) ≅
      coinvariantTensorTotal ρ σ :=
  coinvariantTensorTotalIso (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) ≪≫
    coinvariantGroupChangeComplexIso e (representationCochainComplex (tensorComplexAction ρ σ)) ≪≫
      (coinvariantTensorTotalIso ρ σ).symm

namespace BarrattEccles
variable {A : Type u} [CommRing A] (X Y : Complex A)
attribute [local instance] Classical.propDecidable

/-- 安定化群で読む一つの軌道の入力と、制限した指定係数の全複体。 -/
abbrev orbitCoefficientComplex (r : ℕ) (k : ULift.{u} (Fin (r + 1))) :=
  (inputCoinvariantTotalFunctor
    (((Rep.resFunctor (binaryTensorPatternSubgroup r k).subtype).mapHomologicalComplex
      (.up ℤ)).obj (arityRepresentationCochain A r))).obj (binaryTensorOrbitInput X Y r k)

/-- 実際の Schur arity の入力を、その指定された軌道直和へ分解する。 -/
def schurArityOrbitIso (r : ℕ) :
    arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) (X ⊞ Y)) r ≅
      ∐ (orbitCoefficientComplex X Y r) :=
  schurArityInputCoefficientIso A (X ⊞ Y) r ≪≫
    ((Rep.coinvariantsTensor A (ULift.{u} (Equiv.Perm (Fin r)))).map₂CochainComplex.flip.obj
      (arityRepresentationCochain A r)).mapIso (binaryTensorFullInputSequenceIso A X Y r) ≪≫
    (inputCoinvariantTotalFunctor (arityRepresentationCochain A r)).mapIso
      (binaryTensorOrbitComplexIso X Y r).symm ≪≫
    inputCoinvariantTotalCoproductIso (binaryTensorOrbitInducedComplex X Y r)
      (arityRepresentationCochain A r) ≪≫
    Sigma.mapIso (fun k => inducedCoinvariantTotalIso (binaryTensorPatternSubgroup r k).subtype
      (binaryTensorOrbitInput X Y r k) (arityRepresentationCochain A r))

/-- 標準代表の群と指定二色部分群の同定を、入力と係数の全複体へ運ぶ。 -/
def orbitStandardCoefficientIso (m n : ℕ) :
    orbitCoefficientComplex X Y (m + n) (ULift.up ⟨m, by omega⟩) ≅
      ((twoColorInputTotalFunctor A m n).obj (twoColorSeparatedInput X Y m n)).obj
        (twoColorSourceCochain A m n) := by
  let k : ULift.{u} (Fin (m + n + 1)) := ULift.up ⟨m, by omega⟩
  let e := (binaryTensorPatternGroupEquiv m n).symm
  let ρ := binaryTensorWordFixedAction X Y (m + n) (binaryTensorCountPattern (m + n) k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin (m + n))) ≃*
      Equiv.Perm (Fin (m + n))).toMonoidHom.comp (binaryTensorPatternSubgroup (m + n) k).subtype)
    (fun g => g.property)
  let σ := (arityComplexAction A (m + n)).comp (binaryTensorPatternSubgroup (m + n) k).subtype
  refine (coinvariantTotalGroupChangeIso e ρ σ).symm ≪≫ ?_
  exact ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).map₂CochainComplex.mapIso
    (twoColorOrbitStandardInputIso X Y m n ≪≫ twoColorStandardSeparatedIso X Y m n)).app
      (twoColorSourceCochain A m n)

/-- 一つの実際の軌道成分で、指定係数射は二つの Schur 成分への鎖ホモトピー同値となる。 -/
def orbitCoefficientComparisonEquiv (m n : ℕ) :
    HomotopyEquiv (orbitCoefficientComplex X Y (m + n) (ULift.up ⟨m, by omega⟩))
      (arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) X) m ⊗
        arityCoinvariantComplex (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A (sequence A) Y) n) :=
  (HomotopyEquiv.ofIso (orbitStandardCoefficientIso X Y m n)).trans
    ((twoColorComplexInputHomotopyEquiv A m n (twoColorSeparatedInput X Y m n)).trans
      (HomotopyEquiv.ofIso (twoColorTargetSchurIso A X Y m n)))

end BarrattEccles
end SerrePositivity.EInfinity
