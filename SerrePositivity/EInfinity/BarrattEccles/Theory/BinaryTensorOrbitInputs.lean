module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorInputDecomposition
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorWordCounts
public import SerrePositivity.EInfinity.BarrattEccles.Theory.FiniteInductionMatrix
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# 固定 arity の二色軌道の入力表現

HA 3.2.4.7 の自由比較に使う。左入力数で標準代表を取り、
各代表の安定化群から誘導した入力の包含・射影を、実際のテンソル冪へ作る。
群作用と微分は既存の複体のものを使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A) (r : ℕ)

/-- 標準代表を固定する、実際の対称群の部分群。 -/
def binaryTensorPatternSubgroup (k : ULift.{u} (Fin (r + 1))) :
    Subgroup (ULift.{u} (Equiv.Perm (Fin r))) :=
  (MulAction.stabilizer (Equiv.Perm (Fin r)) (binaryTensorCountPattern r k.down)).comap
    MulEquiv.ulift.toMonoidHom

/-- 固定 arity の和のテンソル冪の、実際の対称群作用の複体。 -/
def binaryTensorFullInput :
    CochainComplex (Rep.{u} A (ULift.{u} (Equiv.Perm (Fin r)))) ℤ :=
  representationCochainComplex (binaryTensorPowerAction X Y r MulEquiv.ulift.toMonoidHom)

/-- 安定化群の作用を持つ、標準代表の入力複体。 -/
def binaryTensorOrbitInput (k : ULift.{u} (Fin (r + 1))) :=
  binaryTensorWordFixedRepresentation X Y r (binaryTensorCountPattern r k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
      Equiv.Perm (Fin r)).toMonoidHom.comp (binaryTensorPatternSubgroup r k).subtype)
    (fun g => (show g.val.down • binaryTensorCountPattern r k.down = _ from g.property))

/-- 標準代表の指定包含を、制限された表現の複体の射とする。 -/
def binaryTensorOrbitInputInclusion (k : ULift.{u} (Fin (r + 1))) :
    binaryTensorOrbitInput X Y r k ⟶
      ((Rep.resFunctor (binaryTensorPatternSubgroup r k).subtype).mapHomologicalComplex
        (.up ℤ)).obj (binaryTensorFullInput X Y r) :=
  binaryTensorFixedRepresentationInclusion X Y r (binaryTensorCountPattern r k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
      Equiv.Perm (Fin r)).toMonoidHom.comp (binaryTensorPatternSubgroup r k).subtype)
    (fun g => (show g.val.down • binaryTensorCountPattern r k.down = _ from g.property))

/-- 標準代表の指定射影を、制限された表現の複体の射とする。 -/
def binaryTensorOrbitInputProjection (k : ULift.{u} (Fin (r + 1))) :
    ((Rep.resFunctor (binaryTensorPatternSubgroup r k).subtype).mapHomologicalComplex
      (.up ℤ)).obj (binaryTensorFullInput X Y r) ⟶ binaryTensorOrbitInput X Y r k :=
  binaryTensorFixedRepresentationProjection X Y r (binaryTensorCountPattern r k.down)
    ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
      Equiv.Perm (Fin r)).toMonoidHom.comp (binaryTensorPatternSubgroup r k).subtype)
    (fun g => (show g.val.down • binaryTensorCountPattern r k.down = _ from g.property))

/-- 指定包含と射影の対角成分は恒等射。 -/
lemma binaryTensorOrbitInput_diagonal (k : ULift.{u} (Fin (r + 1))) (i : ℤ) :
    (binaryTensorOrbitInputInclusion X Y r k).f i ≫
      (binaryTensorOrbitInputProjection X Y r k).f i = 𝟙 _ := by
  apply (forget₂ (Rep.{u} A (binaryTensorPatternSubgroup r k)) (ModuleCat A)).map_injective
  exact congrArg (fun f => f.f i)
    (binaryTensorWordInclusion_projection X Y r (binaryTensorCountPattern r k.down))

set_option maxHeartbeats 800000 in
-- 次数ごとの表現を実際の複体作用と比較する定義展開に必要。
/-- 同じ軌道の標準代表でも、安定化群の外の行列成分は零。 -/
lemma binaryTensorOrbitInput_self (k : ULift.{u} (Fin (r + 1))) (i : ℤ)
    (g : ULift.{u} (Equiv.Perm (Fin r))) (hg : g ∉ binaryTensorPatternSubgroup r k)
    (x : (binaryTensorOrbitInput X Y r k).X i) :
    ((binaryTensorOrbitInputProjection X Y r k).f i).hom
      (((binaryTensorFullInput X Y r).X i).ρ g
        (((binaryTensorOrbitInputInclusion X Y r k).f i).hom x)) = 0 := by
  have hc := binaryTensorWordPermutation_component_ne X Y r g.down
    (binaryTensorCountPattern r k.down) (binaryTensorCountPattern r k.down) hg
  exact congrArg (fun f => (f.f i).hom x) hc

set_option maxHeartbeats 800000 in
-- 次数ごとの表現を実際の複体作用と比較する定義展開に必要。
/-- 入力数の異なる標準代表の間の行列成分は、全ての置換で零。 -/
lemma binaryTensorOrbitInput_cross (k l : ULift.{u} (Fin (r + 1))) (hkl : k ≠ l) (i : ℤ)
    (g : ULift.{u} (Equiv.Perm (Fin r))) (x : (binaryTensorOrbitInput X Y r k).X i) :
    ((binaryTensorOrbitInputProjection X Y r l).f i).hom
      (((binaryTensorFullInput X Y r).X i).ρ g
        (((binaryTensorOrbitInputInclusion X Y r k).f i).hom x)) = 0 := by
  have hn : binaryTensorWordCount r (binaryTensorCountPattern r k.down) false ≠
      binaryTensorWordCount r (binaryTensorCountPattern r l.down) false := by
    simpa only [binaryTensorCountPattern_count] using
      (fun h => hkl (ULift.ext (Fin.ext h)))
  have hc := binaryTensorWordPermutation_component_ne X Y r g.down
    (binaryTensorCountPattern r k.down) (binaryTensorCountPattern r l.down)
    (binaryTensorWord_smul_ne_of_count_ne r _ _ false hn g.down)
  exact congrArg (fun f => (f.f i).hom x) hc

end SerrePositivity.EInfinity
