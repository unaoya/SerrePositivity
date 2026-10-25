module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSourceGenerators
/-!
概要：元の出発提示の全基底像に追加係数を併合し、同じ κ 上界と全 Hom 包含を保つ。
方針：係数族の直和で基底像と追加係数を保持し、各生成子語を span へ送る。
規約：元の dg 関手の全 Hom を省略せず、追加係数の個数だけを仮定する。
使われ方：c′ の任意閉射に必要な係数を共通の出発提示へ取り込む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (c : DGCategoryPresentationCode R κ)
  {J K : Type u} (D : Type v) [DGCategory R D] (value : J → D)
  (F : DGFunctor R (c.Objects R κ) (DGObjectImage value))
  (extraSource extraTarget : K → J) (extraDegree : K → ℤ)
  (extraCoefficient : ∀ k, GradedHom R (value (extraSource k)) (value (extraTarget k)) (extraDegree k))

abbrev DGCodeAugmentedCoefficientIndex : Type u := DGCodeHomGeneratorIndex R κ c ⊕ K

lemma dgCodeAugmentedCoefficientIndex_cardinal_le (hκ : Cardinal.aleph0 ≤ κ) (hK : Cardinal.mk K ≤ κ) :
    Cardinal.mk (DGCodeAugmentedCoefficientIndex R κ c (K := K)) ≤ κ := by
  simp only [DGCodeAugmentedCoefficientIndex, Cardinal.mk_sum, Cardinal.lift_id]
  exact Cardinal.add_le_of_le hκ (dgCodeHomGeneratorIndex_cardinal_le R κ c hκ) hK

def dgCodeAugmentedSource : DGCodeAugmentedCoefficientIndex R κ c (K := K) → J :=
  Sum.elim (dgCodeGeneratorSource R κ c D value F) extraSource

def dgCodeAugmentedTarget : DGCodeAugmentedCoefficientIndex R κ c (K := K) → J :=
  Sum.elim (dgCodeGeneratorTarget R κ c D value F) extraTarget

def dgCodeAugmentedDegree : DGCodeAugmentedCoefficientIndex R κ c (K := K) → ℤ :=
  Sum.elim (dgCodeGeneratorDegree R κ c) extraDegree

def dgCodeAugmentedCoefficient (i : DGCodeAugmentedCoefficientIndex R κ c (K := K)) :
    GradedHom R (value (dgCodeAugmentedSource R κ c D value F extraSource i))
      (value (dgCodeAugmentedTarget R κ c D value F extraTarget i))
      (dgCodeAugmentedDegree R κ c extraDegree i) :=
  match i with
  | .inl j => dgCodeGeneratorCoefficient R κ c D value F j
  | .inr k => extraCoefficient k

lemma dgCodeAugmentedImage_contains :
    ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
      DGGeneratedHomWord.linearSpan
        (dgCodeAugmentedSource R κ c D value F extraSource)
        (dgCodeAugmentedTarget R κ c D value F extraTarget)
        (dgCodeAugmentedDegree R κ c extraDegree) R D value
        (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
        (F.obj x).label (F.obj y).label n := by
  apply generatedHomImage_of_codeGenerators R κ c _ _ _ D value _ F
  intro x y n b
  exact DGGeneratedHomWord.evaluate_mem_span _ _ _ R D value
    (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
    (.generator (.inl ⟨x, y, ULift.up n, b⟩))

lemma dgCodeAugmentedCoefficient_mem (k : K) :
    extraCoefficient k ∈ DGGeneratedHomWord.linearSpan
      (dgCodeAugmentedSource R κ c D value F extraSource)
      (dgCodeAugmentedTarget R κ c D value F extraTarget)
      (dgCodeAugmentedDegree R κ c extraDegree) R D value
      (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
      (extraSource k) (extraTarget k) (extraDegree k) := by
  have h := DGGeneratedHomWord.evaluate_mem_span
    (dgCodeAugmentedSource R κ c D value F extraSource)
    (dgCodeAugmentedTarget R κ c D value F extraTarget)
    (dgCodeAugmentedDegree R κ c extraDegree) R D value
    (dgCodeAugmentedCoefficient R κ c D value F extraSource extraTarget extraDegree extraCoefficient)
    (.generator (Sum.inr k))
  exact h

end SerrePositivity.DifferentialGraded
