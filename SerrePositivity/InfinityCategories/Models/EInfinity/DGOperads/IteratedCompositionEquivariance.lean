module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Composition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPermutationTail
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionNaturality

/-!
模型。文献の定義との比較は後で
# 全入力への合成の再帰と等変性の接続

概要：Berger–Moerdijk §1 の全入力への合成の等変性に必要な、arity の移送と再帰の因子分解を示す。
方針：arity の等式による置換の移送を関手の自然性として扱い、再帰の一段を一般の代入射へ分解する。
規約：最後の入力から代入し、尾の長さを k+l とする既存の定義を用いる。
使われ方：部分合成の同時等変性と帰納仮定を全入力への合成に適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

/-- 概要：オペラッドの arity の置換作用は arity の等式による移送と両立する（Berger–Moerdijk §1）。
方針：arity の等式で長さを同一視し、置換と等式の射を簡約する。
規約：移送した置換は Fin 上の標準同値による共役。
使われ方：部分合成の前後の arity の括弧付けの変更を等変性に反映する。 -/
lemma arity_permutation_index_eq (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {r s : ℕ} (h : r = s)
    (σ : Equiv.Perm (Fin r)) :
    eqToHom (congrArg P.arity h) ≫
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation s ((finCongr h).permCongr σ)) =
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation r σ) ≫ eqToHom (congrArg P.arity h) := by
  subst s
  have he : (finCongr (Eq.refl r)).permCongr σ = σ := by ext i; rfl
  simp only [he, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 概要：位置 n への部分合成を反復代入の再帰の arity に合わせる（Berger–Moerdijk §1）。
方針：部分合成の始域と終域の長さの括弧付けを、等式の射で移す。
規約：代入した l 個と元の後方 k 個を、長さ k+l の新しい尾として扱う。
使われ方：反復代入の等変性の帰納法で最初の部分合成を表す。 -/
def composeFirstInputInsertion (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k l : ℕ) :
    P.arity (n + 1 + k) ⊗ P.arity l ⟶ P.arity (n + (k + l)) :=
  (eqToHom (congrArg P.arity (by omega : n + 1 + k = n + k + 1)) ▷ P.arity l) ≫
    P.comp (n + k) l ⟨n, by omega⟩ ≫
      eqToHom (congrArg P.arity (Nat.add_assoc n k l))

private lemma tensor_transport {R S L : Complex A} (t : R ⟶ S)
    (a : R ⟶ R) (a' : S ⟶ S) (c : L ⟶ L) (h : a ≫ t = t ≫ a') :
    (a ⊗ₘ c) ≫ (t ▷ L) = (t ▷ L) ≫ (a' ⊗ₘ c) := by
  simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, h]

private lemma compose_three_intertwining {X Y Z W : Complex A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z) (d : W ⟶ W)
    (hf : a ≫ f = f ≫ b) (hg : b ≫ g = g ≫ c) (hh : c ≫ h = h ≫ d) :
    a ≫ (f ≫ g ≫ h) = (f ≫ g ≫ h) ≫ d := by
  rw [← Category.assoc a f, hf, Category.assoc, ← Category.assoc b g, hg,
    Category.assoc, hh]
  simp only [Category.assoc]

/-- 概要：再帰の最初の部分合成は内側置換と後方置換を新しい尾の置換へ送る（Berger–Moerdijk §1）。
方針：部分合成の同時等変性の前後を、arity の移送の自然性で挟む。
規約：前方 n 個の入力は固定し、新しい尾では l 個の挿入入力を先に置く。
使われ方：反復代入の等変性の帰納段階で最初の部分合成の等変性を与える。 -/
lemma composeFirstInputInsertion_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k l : ℕ)
    (τ : Equiv.Perm (Fin l)) (ρ : Equiv.Perm (Fin k)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1 + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (n + 1))) ρ)) ⊗ₘ
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation l τ)) ≫ P.composeFirstInputInsertion n k l =
      P.composeFirstInputInsertion n k l ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation (n + (k + l))
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin n))
            ((finCongr (Nat.add_comm l k)).permCongr (_root_.SerrePositivity.FiniteBijection.blockEquiv τ ρ)))) := by
  have ha := (P.arity_permutation_index_eq
    (by omega : n + 1 + k = n + k + 1)
    (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (n + 1))) ρ)).symm
  have hleft := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.tensor_transport (eqToHom (congrArg P.arity
    (by omega : n + 1 + k = n + k + 1))) _ _
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation l τ)) ha
  have hright : P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + k + l)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation n k l τ ρ)) ≫
      eqToHom (congrArg P.arity (Nat.add_assoc n k l)) =
    eqToHom (congrArg P.arity (Nat.add_assoc n k l)) ≫
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + (k + l))
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin n))
          ((finCongr (Nat.add_comm l k)).permCongr (_root_.SerrePositivity.FiniteBijection.blockEquiv τ ρ)))) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation_reassociate] using
      (P.arity_permutation_index_eq (Nat.add_assoc n k l)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertedTailPermutation n k l τ ρ)).symm
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.compose_three_intertwining
    (eqToHom (congrArg P.arity (by omega : n + 1 + k = n + k + 1)) ▷ P.arity l)
    (P.comp (n + k) l ⟨n, by omega⟩)
    (eqToHom (congrArg P.arity (Nat.add_assoc n k l))) _ _ _ _ hleft
    (P.comp_tail_equivariance n k l τ ρ) hright

/-- 概要：全入力への合成の再帰の一段は最後の係数を先に代入する一般の射に分解できる（Berger–Moerdijk §1）。
方針：部分合成の前後の arity の移送を最初の代入射に含め、whisker の合成則でまとめる。
規約：再帰から戻る arity の移送は残りの合成射の末尾に含める。
使われ方：一般の有限族の代入の等変性を、既存の全入力への合成の再帰に適用する。 -/
lemma composeFirstInputs_succ_factor (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin (n + 1) → ℕ) :
    P.composeFirstInputs (n + 1) k s =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n (fun i => P.arity (s i))
        ((eqToHom (congrArg P.arity (by omega : n + 1 + k = n + k + 1)) ▷
            P.arity (s (Fin.last n))) ≫
          P.comp (n + k) (s (Fin.last n)) ⟨n, by omega⟩ ≫
          eqToHom (congrArg P.arity (Nat.add_assoc n k (s (Fin.last n)))))
        (P.composeFirstInputs n (k + s (Fin.last n)) (fun i => s i.castSucc) ≫
          eqToHom (congrArg P.arity (by rw [Fin.sum_univ_castSucc]; omega :
            (∑ i : Fin n, s i.castSucc) + (k + s (Fin.last n)) = (∑ i, s i) + k))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep,
    comp_whiskerRight, Category.assoc]

/-- 概要：内側演算がない場合の反復代入は尾の置換と両立する（Berger–Moerdijk §1）。
方針：反復代入の基底の右単位子の自然性を使う。
規約：空の有限族の arity の総和は 0。
使われ方：全入力への合成の等変性の帰納法の基底となる。 -/
lemma composeFirstInputs_zero_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (k : ℕ) (s : Fin 0 → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) (ρ : Equiv.Perm (Fin k)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (0 + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 0)) ρ)) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap 0 (fun i => P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)))) ≫
          P.composeFirstInputs 0 k s =
      P.composeFirstInputs 0 k s ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation ((∑ i, s i) + k)
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation 0 s τ) ρ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.sum_univ_zero, eqToHom_refl, Category.comp_id, tensorHom_id]
  exact rightUnitor_naturality (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (0 + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 0)) ρ)))

private lemma compose_intertwining {X Y Z : Complex A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : X ⟶ X) (b : Y ⟶ Y) (c : Z ⟶ Z)
    (hf : a ≫ f = f ≫ b) (hg : b ≫ g = g ≫ c) :
    a ≫ (f ≫ g) = (f ≫ g) ≫ c := by
  rw [← Category.assoc, hf, Category.assoc, hg, Category.assoc]

/-- 概要：先頭の各入力への反復代入は内側の各置換と未代入の尾の置換に関して等変である（Berger–Moerdijk §1）。
方針：最後の内側演算を分離し、その部分合成の等変性と残りの反復代入の帰納仮定を使う。
規約：尾の入力を k 個残し、出力では各内側ブロックと尾に独立に置換を作用させる。
使われ方：自由代数の作用を各入力の coinvariant 関係に沿って降ろす。 -/
lemma composeFirstInputs_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n k : ℕ) (s : Fin n → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) (ρ : Equiv.Perm (Fin k)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin n)) ρ)) ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)))) ≫
          P.composeFirstInputs n k s =
      P.composeFirstInputs n k s ≫ P.sequence.map
        (_root_.SerrePositivity.FiniteBijection.permutation ((∑ i, s i) + k)
          (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ) ρ)) := by
  induction n generalizing k with
  | zero => exact P.composeFirstInputs_zero_equivariance k s τ ρ
  | succ n ih =>
    let l := s (Fin.last n)
    let ρ' : Equiv.Perm (Fin (k + l)) :=
      (finCongr (Nat.add_comm l k)).permCongr (_root_.SerrePositivity.FiniteBijection.blockEquiv (τ (Fin.last n)) ρ)
    let hfin : (∑ i : Fin n, s i.castSucc) + (k + l) = (∑ i, s i) + k := by
      dsimp [l]
      rw [Fin.sum_univ_castSucc]
      omega
    let q := eqToHom (congrArg P.arity hfin)
    let recursiveMap := P.composeFirstInputs n (k + l) (fun i => s i.castSucc)
    let d := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + (k + l))
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin n)) ρ'))
    let e₀ := P.sequence.map
      (_root_.SerrePositivity.FiniteBijection.permutation ((∑ i : Fin n, s i.castSucc) + (k + l))
        (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc)) ρ'))
    let e := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((∑ i, s i) + k)
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation (n + 1) s τ) ρ))
    have hpost : e₀ ≫ q = q ≫ e := by
      have h := (P.arity_permutation_index_eq hfin
        (_root_.SerrePositivity.FiniteBijection.blockEquiv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc)) ρ')).symm
      have hp : (finCongr hfin).permCongr
          (_root_.SerrePositivity.FiniteBijection.blockEquiv
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n (fun i => s i.castSucc) (fun i => τ i.castSucc)) ρ') =
          _root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation (n + 1) s τ) ρ := by
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation_tail_splitLast n k s τ ρ
      rw [hp] at h
      exact h
    have hg : (d ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
        P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i.castSucc) (τ i.castSucc)))) ≫
          (recursiveMap ≫ q) = (recursiveMap ≫ q) ≫ e :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.compose_intertwining recursiveMap q _ e₀ e
        (ih (k + l) (fun i => s i.castSucc) (fun i => τ i.castSucc) ρ') hpost
    have hstep := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep_equivariance n (fun i => P.arity (s i))
      (P.composeFirstInputInsertion n k l) (recursiveMap ≫ q)
      (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1 + k)
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin (n + 1))) ρ)))
      (fun i => P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i))) d e
      (P.composeFirstInputInsertion_equivariance n k l (τ (Fin.last n)) ρ) hg
    rw [P.composeFirstInputs_succ_factor]
    exact hstep

/-- 概要：全入力への合成は各内側演算の置換に関して等変である（Berger–Moerdijk §1）。
方針：尾を空にした反復代入の等変性を用い、始域と終域の arity の移送を処理する。
規約：出力の置換は内側の各入力ブロックの置換を連結したもの。
使われ方：自由代数の演算を内側の各入力の coinvariant 関係に沿って降ろす。 -/
lemma composition_inner_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) (s : Fin n → ℕ)
    (τ : ∀ i, Equiv.Perm (Fin (s i))) :
    (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i =>
      P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)))) ≫ P.composition n s =
        P.composition n s ≫ P.sequence.map
          (_root_.SerrePositivity.FiniteBijection.permutation (∑ i, s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ)) := by
  let b := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (s i) (τ i)))
  let t := eqToHom (congrArg P.arity (Nat.add_zero n).symm)
  let q := eqToHom (congrArg P.arity (Nat.add_zero (∑ i, s i)))
  let e₀ := P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation ((∑ i, s i) + 0)
    (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ) (1 : Equiv.Perm (Fin 0))))
  have ht : (P.arity n ◁ b) ≫ (t ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) =
      (t ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i))) ≫ (P.arity (n + 0) ◁ b) :=
    whisker_exchange t b
  have hr : (P.arity (n + 0) ◁ b) ≫ P.composeFirstInputs n 0 s =
      P.composeFirstInputs n 0 s ≫ e₀ := by
    have h := P.composeFirstInputs_equivariance n 0 s τ 1
    have hp : _root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin n)) (1 : Equiv.Perm (Fin 0)) =
        (1 : Equiv.Perm (Fin (n + 0))) := _root_.SerrePositivity.FiniteBijection.blockEquiv_refl n 0
    rw [hp, _root_.SerrePositivity.FiniteBijection.permutation_one, P.sequence.map_id, id_tensorHom] at h
    exact h
  have hq : e₀ ≫ q = q ≫ P.sequence.map
      (_root_.SerrePositivity.FiniteBijection.permutation (∑ i, s i) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ)) := by
    have h := (P.arity_permutation_index_eq (Nat.add_zero (∑ i, s i))
      (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ) (1 : Equiv.Perm (Fin 0)))).symm
    have hp : (finCongr (Nat.add_zero (∑ i, s i))).permCongr
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ) (1 : Equiv.Perm (Fin 0))) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ := by
      change (finCongr (Nat.add_zero (∑ i, s i))).permCongr
        (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyPermutation n s τ) (Equiv.refl (Fin 0))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_zero_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_trans]
      rfl
    rw [hp] at h
    exact h
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.compose_three_intertwining (t ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => P.arity (s i)))
    (P.composeFirstInputs n 0 s) q _ _ e₀ _ ht hr hq

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
