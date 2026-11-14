module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriple
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorThreeSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCandidateTwoSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataLowDimensionalPullback
/-!
概要：単射に沿う候補の辺・三点成分と二単体への制限を比較し、実三単体の全面を同定する。
方針：元の実 Hom 成分の単射制限を tensor の二項式へ移し、二点・三点で全データを照合する。
規約：非単射への自然性や全次元 HA は別途証明する。使われ方：二入力 dg nerve の tensor 写像。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
/-- 単射による生のデータの辺成分の制限は、同じ像の辺である。 -/
lemma dgNerveData_pullback_edgeHom (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (a b : Fin (m + 1)) (hab : a < b) :
    (s.pullback α).edgeHom a b hab =
      s.edgeHom (α a) (α b) ((α.monotone.strictMono_of_injective hα) hab) := by
  exact eq_of_heq (s.edgeHom_heq_of_pullback_eq (s.pullback α) α hα rfl a b hab
    ((α.monotone.strictMono_of_injective hα) hab)).symm
/-- 単射による生のデータの三点成分の制限は、同じ像の三点成分である。 -/
lemma dgNerveData_pullback_tripleHom (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (a b c : Fin (m + 1)) (hab : a < b) (hbc : b < c) :
    (s.pullback α).tripleHom a b c hab hbc =
      s.tripleHom (α a) (α b) (α c) ((α.monotone.strictMono_of_injective hα) hab)
        ((α.monotone.strictMono_of_injective hα) hbc) := by
  exact eq_of_heq (s.tripleHom_heq_of_pullback_eq (s.pullback α) α hα rfl a b c hab hbc
    ((α.monotone.strictMono_of_injective hα) hab)
    ((α.monotone.strictMono_of_injective hα) hbc)).symm
variable (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- tensor 候補の三点成分は任意の単射に沿う制限を保つ。 -/
lemma dgNerveTensorDataCandidate_pullback_tripleHom {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (a b c : Fin (m + 1)) (hab : a < b) (hbc : b < c) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).tripleHom a b c hab hbc =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).tripleHom a b c hab hbc := by
  rw [dgNerveData_pullback_tripleHom R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t) α hα a b c hab hbc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_tripleHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_tripleHom,
    dgNerveData_pullback_edgeHom R B s α hα a c (hab.trans hbc),
    dgNerveData_pullback_tripleHom R C t α hα a b c hab hbc,
    dgNerveData_pullback_tripleHom R B s α hα a b c hab hbc,
    dgNerveData_pullback_edgeHom R C t α hα b c hbc,
    dgNerveData_pullback_edgeHom R C t α hα a b hab]
/-- tensor 候補の辺成分は任意の単射に沿う制限を保つ。 -/
lemma dgNerveTensorDataCandidate_pullback_edgeHom {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (a b : Fin (m + 1)) (hab : a < b) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).edgeHom a b hab =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).edgeHom a b hab := by
  rw [dgNerveData_pullback_edgeHom R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t) α hα a b hab]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_edgeHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_edgeHom,
    dgNerveData_pullback_edgeHom R B s α hα a b hab,
    dgNerveData_pullback_edgeHom R C t α hα a b hab]
/-- 任意の単射による二単体への制限で、tensor 候補の全データは一致する。 -/
lemma dgNerveTensorDataCandidate_pullback_two {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (α : Fin 3 →o Fin (n + 1)) (hα : Function.Injective α) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
    (s := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α)
    (t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)) rfl
  apply heq_of_eq
  funext I a b k hI ha hb hk
  by_cases hc : I.card = 3
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_eq_univ I hc
    subst I
    have ha' : a = 0 :=
      ha.trans ((Finset.min'_eq_iff _ _ 0).2 ⟨by simp, fun x _ => Fin.zero_le x⟩)
    have hb' : b = 2 :=
      hb.trans ((Finset.max'_eq_iff _ _ 2).2 ⟨by simp, fun x _ => Fin.le_last x⟩)
    have hk' : k = -1 := by simpa using hk
    subst ha' hb' hk'
    have h := dgNerveTensorDataCandidate_pullback_tripleHom R B C s t α hα 0 1 2
      (by decide) (by decide)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom,
      show ({0, 1, 2} : Finset (Fin 3)) = Finset.univ from by decide] using! h
  · have hle := Finset.card_le_univ I
    simp only [Fintype.card_fin] at hle
    have hc2 : I.card = 2 := by omega
    have hab : a < b := by
      have h := I.min'_lt_max'_of_card (by omega)
      simpa only [← ha, ← hb] using h
    have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc2
      (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _)
    have hk' : k = 0 := by omega
    subst hk'
    subst I
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom] using!
      dgNerveTensorDataCandidate_pullback_edgeHom R B C s t α hα a b hab
/-- 実 tensor 三単体の単射による二単体への制限は、入力の同じ制限の tensor。 -/
lemma dgTensorThreeSimplex_pullbackTwo (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3)
    (α : Fin 3 →o Fin 4) (hα : Function.Injective α) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorThreeSimplex R B C s t).pullback α =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C (s.pullback α) (t.pullback α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).pullback α = _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_two R B C (s.pullback α) (t.pullback α)]
  exact dgNerveTensorDataCandidate_pullback_two R B C s.toSimplexData t.toSimplexData α hα
/-- 実 tensor 三単体の四つの面は、入力の同じ面の実 tensor 二単体に厳密に一致する。 -/
lemma dgTensorThreeSimplex_face (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3) (i : Fin 4) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGTensorCategory R B C)).δ i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorThreeSimplex R B C s t) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTwoSimplex R B C ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R B).δ i s) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C).δ i t) := by
  exact dgTensorThreeSimplex_pullbackTwo R B C s t (SimplexCategory.δ i).toOrderHom
    (show Function.Injective i.succAbove from Fin.succAbove_right_injective)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
