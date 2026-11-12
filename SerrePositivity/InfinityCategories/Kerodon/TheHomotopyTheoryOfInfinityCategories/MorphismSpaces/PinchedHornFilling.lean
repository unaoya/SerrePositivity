module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearEquationTransfer
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearResidual

/-! # 右 pinched ホーンの直接の線形充填

概要：既知の面を保持し、最上位を零、欠けた面を削除和の明示解とする。
方針：既知の方程式は面から移送し、欠けた面は削除残差の恒等式で検証する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：右 pinched 写像空間の Kan 性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：元のホーン面に制限される族は、二つの未知集合以外で方程式を満たす。
方針：集合を含む利用可能な面を選び、その逆像の方程式を単射で移送する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：充填候補で未検証の方程式を二つに限定する。 -/
lemma equation_of_faces {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1))
    (hfaces : ∀ j (hji : j ≠ i),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData σ j hji)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) :
    differential A (f.component I k hI hk) = f.rhs I k hk := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hfull hmissing
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hfull hmissing
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : J.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact hI.card_pos)
  have hImage : J.image j.succAbove = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (σ.app _ (SSet.horn.face i j hji))).equation J k hJ
    (by rw [hcard]; exact hk)
  change differential A ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData σ j hji).component J k hJ _) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData σ j hji).rhs J k _ at hh
  rw [← hfaces j hji] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_rhs_of_inj _ _ _ _ _ j.succAboveOrderEmb.injective.injOn] at hh
  have hImage' : J.image j.succAboveOrderEmb.toOrderHom = I := hImage
  simpa only [hImage'] using hh

/-- 概要：充填候補は欠けた面の成分だけを削除和の明示解に置き換える。
方針：他の全成分は回収した既知族を保ち、最上位は零のままにする。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：全てのホーン番号に共通の充填データ。 -/
def fillerData {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1) := fun t =>
  if t.val.1 = Finset.univ.erase i then
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution Finset.univ i
      (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ).componentOrZero (Finset.univ.erase j) t.val.2)
  else _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ t

/-- 概要：欠けた面以外の成分は充填候補への置換で変わらない。
方針：置換の条件分岐の偽の側を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：既知面と最上位成分の検証。 -/
lemma fillerData_component_of_ne {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (J : Finset (Fin (n + 2))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hne : J ≠ Finset.univ.erase i) :
    (fillerData σ).component J k hJ hk = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ).component J k hJ hk := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, fillerData, ite_eq_right hne]

/-- 概要：充填候補を利用可能な面に制限すると元のホーン面の線形族に戻る。
方針：その面の全ての像集合は欠けた面ではないので、既知族の面の計算に戻す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：既知の全方程式と面の一致。 -/
lemma fillerData_pullback_face {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (fillerData σ) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData σ j hji := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData_pullback_face σ j hji]
  funext t
  rcases t with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (fillerData σ)).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ)).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact fillerData_component_of_ne σ _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.image_known j hji J).2

/-- 概要：充填候補の最上位成分は零。
方針：全体集合は欠けた面ではなく、既知族の全体成分は零である。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：最上位方程式の左辺の検証。 -/
lemma fillerData_top_zero {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (k : ℤ) (hJ : (Finset.univ : Finset (Fin (n + 2))).Nonempty)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    (fillerData σ).component Finset.univ k hJ hk = 0 := by
  have hne : (Finset.univ : Finset (Fin (n + 2))) ≠ Finset.univ.erase i := by
    intro h
    have hi : i ∈ (Finset.univ : Finset (Fin (n + 2))) := Finset.mem_univ _
    rw [h] at hi
    exact Finset.notMem_erase _ _ hi
  rw [fillerData_component_of_ne σ _ _ _ _ hne]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData, ne_eq, not_true_eq_false, dite_false]

/-- 概要：欠けた面以外では全域化した成分も置換で変わらない。
方針：空集合と不適切な次数は零、適切な成分は既知成分の保存を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：明示解の他の面の寄与の比較。 -/
lemma fillerData_componentOrZero_of_ne {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (J : Finset (Fin (n + 2))) (k : ℤ) (hne : J ≠ Finset.univ.erase i) :
    (fillerData σ).componentOrZero J k = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ).componentOrZero J k := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero
  split_ifs with hJ hk
  · exact fillerData_component_of_ne σ J k hJ hk hne
  · rfl
  · rfl

/-- 概要：欠けた面の成分は、既知の他の面から作る削除和の明示解。
方針：置換の真の条件分岐を評価する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：最上位右辺の相殺。 -/
lemma fillerData_missing_component {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (k : ℤ) (hJ : (Finset.univ.erase i).Nonempty)
    (hk : k = 1 - ((Finset.univ.erase i).card : ℤ)) :
    (fillerData σ).component (Finset.univ.erase i) k hJ hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution Finset.univ i
        (fun j => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.knownData σ).componentOrZero (Finset.univ.erase j) k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, fillerData, ite_true]

/-- 概要：充填候補の最上位右辺は零。
方針：欠けた面の成分を明示解に同定し、他の削除成分の不変性で相殺補題を使う。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：最上位と欠けた面の方程式。 -/
lemma fillerData_top_rhs_zero {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    (fillerData σ).rhs Finset.univ k hk = 0 := by
  have hfull : 2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp
  have hM := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hfull i (Finset.mem_univ _)
  have hkM : k + 1 = 1 - ((Finset.univ.erase i).card : ℤ) := by
    have := Finset.card_erase_add_one (Finset.mem_univ i)
    omega
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rhs_eq_zero_of_deletionSolution _ _ _ _ i (Finset.mem_univ _)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.componentOrZero_eq _ _ _ hM hkM, fillerData_missing_component]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  dsimp only
  rw [fillerData_componentOrZero_of_ne σ _ _
    (fun he => hji ((Finset.erase_inj _ (Finset.mem_univ j)).mp he))]

/-- 概要：充填候補の欠けた面自身も線形方程式を満たす。
方針：最上位右辺は零、他の削除面は既知の方程式を満たすので残差恒等式を適用する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：充填候補を実際の線形単体にする最後の方程式。 -/
lemma fillerData_missing_equation {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) :
    differential A ((fillerData σ).component (Finset.univ.erase i) (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty (by simp) i (Finset.mem_univ _))
      (by have := Finset.card_erase_add_one (Finset.mem_univ i); omega)) =
    (fillerData σ).rhs (Finset.univ.erase i) (k + 1)
      (by have := Finset.card_erase_add_one (Finset.mem_univ i); omega) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.missing_equation _ Finset.univ k (by simp) hk i (Finset.mem_univ _)
    (fillerData_top_rhs_zero σ k hk)
  intro j hji
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.residual_eq_zero_iff _ _ _ _ _).mpr
  exact equation_of_faces σ _ (fillerData_pullback_face σ) _ _ _ _
    (Finset.erase_ssubset (Finset.mem_univ j.val)).ne
    (fun he => hji ((Finset.erase_inj _ (Finset.mem_univ j.val)).mp he))

/-- 概要：充填候補は全ての非空部分集合で線形方程式を満たす。
方針：全体集合・欠けた面・既知集合の三場合に分けて証明済みの方程式を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：任意のホーンの無条件の線形充填。 -/
lemma fillerData_mem {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    fillerData σ ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule A x y (n + 1) := by
  intro J k hJ hk
  by_cases hf : J = Finset.univ
  · subst J
    rw [fillerData_top_zero σ k hJ hk, fillerData_top_rhs_zero σ k hk]
    exact map_zero _
  · by_cases hm : J = Finset.univ.erase i
    · subst J
      have hdeg : k = (1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) + 1 := by
        have := Finset.card_erase_add_one (Finset.mem_univ i)
        omega
      have hkTop : k - 1 = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ) := by omega
      have hh := fillerData_missing_equation σ (k - 1) hkTop
      have htransport : ∀ (l : ℤ) (hl : l = k)
          (hd : l = 1 - ((Finset.univ.erase i).card : ℤ)),
          (differential A ((fillerData σ).component (Finset.univ.erase i) l hJ hd) =
            (fillerData σ).rhs (Finset.univ.erase i) l hd) →
          differential A ((fillerData σ).component (Finset.univ.erase i) k hJ hk) =
            (fillerData σ).rhs (Finset.univ.erase i) k hk := by
        intro l hl
        subst l
        exact fun _ he => he
      exact htransport (k - 1 + 1) (by omega) (by omega) hh
    · exact equation_of_faces σ _ (fillerData_pullback_face σ) J k hJ hk hf hm

/-- 概要：任意の右 pinched ホーンに対する線形方程式の充填単体。
方針：明示候補と全方程式の検証を解の部分加群の元にまとめる。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：実際の右 pinched 単体への再構成。 -/
def filler {n : ℕ} {i : Fin (n + 2)}
    (σ : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y (n + 1) := ⟨fillerData σ, fillerData_mem σ⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling
