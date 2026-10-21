module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugMixedEquation
/-!
概要：同相の実候補係数を元の同じ dg 関手の係数へ移す。
方針：二つの相で選ぶ実 dg 関手と線形 Hom 移送を使い、全域係数の零分岐も照合する。
規約：同相の HA 方程式は次工程。使われ方：全候補単体の HA 方程式の完成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 相で選ぶ、元の同じ実比較対象射影または入力像の dg 関手。 -/
def dgCommaAugmentationPhaseFunctor (p : Fin 2) :
    DGFunctor R (DGFunctorCommaObject R C E F) E :=
  Fin.cases (dgCommaAugmentationSource R C E F) (fun _ ↦ dgCommaAugmentationTarget R C E F) p
variable {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 実候補の同相対象は、相で選んだ同じ実 dg 関手の像。 -/
lemma dgCommaAugmentationPrismData_obj_phase
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (a : Fin (n + 1)) (ha : β a = p) :
    (dgCommaAugmentationPrismData R C E F s β).obj a =
      (dgCommaAugmentationPhaseFunctor R C E F p).obj (s.obj a) := by
  fin_cases p
  · exact dgCommaAugmentationPrismData_obj_zero R C E F s β a ha
  · exact dgCommaAugmentationPrismData_obj_one R C E F s β a ha
/-- 同相の実候補係数は、相で選んだ同じ実 dg 関手の斉次像。 -/
lemma dgCommaAugmentationPrismData_hom_phase
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hpa : β a = p) (hpb : β b = p) :
    HEq ((dgCommaAugmentationPrismData R C E F s β).hom I a b k hI ha hb hk)
      (((dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) := by
  fin_cases p
  · exact dgCommaAugmentationPrismData_hom_zero R C E F s β I a b k hI ha hb hk hpa hpb
  · exact dgCommaAugmentationPrismData_hom_one R C E F s β I a b k hI ha hb hk hpa hpb
/-- 同相の実候補 Hom から元の相関手の Hom への同じ線形移送。 -/
def dgCommaAugmentationSameTransport (β : Fin (n + 1) →o Fin 2) (p : Fin 2)
    (a b : Fin (n + 1)) (k : ℤ) (hpa : β a = p) (hpb : β b = p) :
    GradedHom R ((dgCommaAugmentationPrismData R C E F s β).obj a)
      ((dgCommaAugmentationPrismData R C E F s β).obj b) k ≃ₗ[R]
      GradedHom R ((dgCommaAugmentationPhaseFunctor R C E F p).obj (s.obj a))
        ((dgCommaAugmentationPhaseFunctor R C E F p).obj (s.obj b)) k :=
  gradedHomTransport (dgCommaAugmentationPrismData_obj_phase R C E F s β p a hpa)
    (dgCommaAugmentationPrismData_obj_phase R C E F s β p b hpb) rfl
/-- 同相の全域係数は、不正な添字の零も含めて同じ相関手の像へ移る。 -/
lemma dgCommaAugmentationSameTransport_homOrZero
    (β : Fin (n + 1) →o Fin 2) (p : Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hpa : β a = p) (hpb : β b = p) :
    dgCommaAugmentationSameTransport R C E F s β p a b k hpa hpb
        ((dgCommaAugmentationPrismData R C E F s β).homOrZero I a b k) =
      ((dgCommaAugmentationPhaseFunctor R C E F p).map (s.obj a) (s.obj b)).f k
        (s.homOrZero I a b k) := by
  unfold SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · exact gradedHomTransport_eq_of_heq
      (dgCommaAugmentationPrismData_obj_phase R C E F s β p a hpa)
      (dgCommaAugmentationPrismData_obj_phase R C E F s β p b hpb) rfl _ _
      (dgCommaAugmentationPrismData_hom_phase R C E F s β p I a b k hI ha hb hk hpa hpb)
  all_goals simp only [map_zero]
end SerrePositivity.InfinityCategories
