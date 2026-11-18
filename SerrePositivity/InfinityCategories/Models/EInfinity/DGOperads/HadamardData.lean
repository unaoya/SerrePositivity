module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HadamardCoherence

/-!
模型。文献の定義との比較は後で
# オペラッドの Hadamard 積のデータ

概要：Berger–Moerdijk §1 の arity ごとのテンソル積に単位と部分合成を与える。
方針：対称列を各対象でテンソルし、tensorμ で部分合成を分離する。
規約：非有界コチェイン複体の既存の Koszul 対称性を用いる。
使われ方：オペラッドの公理を検証し Hopf 対角の終域を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：二つの対称列を arity ごとにテンソルする（Berger–Moerdijk §1）。
方針：対象・射の両方を既存のテンソル関手で写す。
規約：arity 0 と有限全単射の作用を含む。
使われ方：Hadamard オペラッドの底の対称列となる。 -/
def sequence (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : _root_.SerrePositivity.SymmetricSequence (Complex A) where
  obj S := P.sequence.obj S ⊗ Q.sequence.obj S
  map σ := P.sequence.map σ ⊗ₘ Q.sequence.map σ
  map_id S := by simp only [P.sequence.map_id, Q.sequence.map_id,
    tensorHom_id, id_whiskerRight]
  map_comp σ τ := by
    rw [P.sequence.map_comp, Q.sequence.map_comp, tensorHom_comp_tensorHom]

/-- 概要：テンソル積の単位演算（Berger–Moerdijk §1）。
方針：テンソル単位を二つに分けて元の単位を適用する。
規約：分離射は単位対象の左単位子の逆射。
使われ方：Hadamard 積の単位となる。 -/
def unit (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : 𝟙_ (Complex A) ⟶ _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) 1 :=
  (λ_ (𝟙_ (Complex A))).inv ≫ (P.unit ⊗ₘ Q.unit)

/-- 概要：テンソル積の部分合成（Berger–Moerdijk §1）。
方針：四因子を分離して各オペラッドの部分合成を適用する。
規約：入力位置と arity は二列で同じものを使う。
使われ方：Hopf 対角の部分合成保存則の終域を与える。 -/
def comp (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (i : Fin (m + 1)) :
    _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) (m + 1) ⊗
      _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) n ⟶
      _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) (m + n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp m n i) (Q.comp m n i)

/-- 概要：arity の等式による移送は二列へ分離する（Berger–Moerdijk §1）。
方針：等式を帰納して恒等射のテンソルに帰着する。
規約：等式の証明の選び方によらない。
使われ方：単位則・結合則に現れる arity の移送を処理する。 -/
lemma transport (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q)) h) =
      eqToHom (congrArg P.arity h) ⊗ₘ eqToHom (congrArg Q.arity h) := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight]
  rfl

/-- 概要：arity の移送と右テンソルは可換である（Berger–Moerdijk §1）。
方針：等式を帰納して恒等射へ帰着する。
規約：右側の arity は移送しない。
使われ方：独立な二代入の中間の arity を各列へ分離する。 -/
lemma transport_right (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {m n : ℕ} (h : m = n) (k : ℕ) :
    eqToHom (congrArg (fun q => _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) q ⊗
      _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) k) h) =
    (eqToHom (congrArg P.arity h) ⊗ₘ eqToHom (congrArg Q.arity h)) ▷
      (P.arity k ⊗ Q.arity k) := by
  subst n
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight]
  rfl

/-- 概要：Hadamard 積の左単位則（Berger–Moerdijk §1）。
方針：tensorμ の自然性で二列に分け、各列の単位則を適用する。
規約：arity 0 を含む。
使われ方：Hadamard オペラッドの公理となる。 -/
lemma unit_comp (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.unit P Q ▷ _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q 0 n 0 ≫
      eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q)) (Nat.zero_add n)) =
      (λ_ (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) n)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.transport P Q (Nat.zero_add n)]
  change (((λ_ (𝟙_ (Complex A))).inv ≫ (P.unit ⊗ₘ Q.unit)) ▷
    (P.arity n ⊗ Q.arity n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp 0 n 0) (Q.comp 0 n 0) ≫
    (eqToHom (congrArg P.arity (Nat.zero_add n)) ⊗ₘ
      eqToHom (congrArg Q.arity (Nat.zero_add n))) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair, comp_whiskerRight, Category.assoc]
  rw [tensorμ_natural_left_assoc]
  simp only [tensorHom_comp_tensorHom, P.unit_comp, Q.unit_comp]
  exact (tensor_left_unitality (P.arity n) (Q.arity n)).symm

/-- 概要：Hadamard 積の右単位則（Berger–Moerdijk §1）。
方針：tensorμ の右自然性と各列の右単位則を使う。
規約：全ての入力位置で成り立つ。
使われ方：Hadamard オペラッドの公理となる。 -/
lemma comp_unit (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m : ℕ) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.unit P Q) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m 1 i =
      (ρ_ (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) (m + 1))).hom := by
  change ((P.arity (m + 1) ⊗ Q.arity (m + 1)) ◁
    ((λ_ (𝟙_ (Complex A))).inv ≫ (P.unit ⊗ₘ Q.unit))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (P.comp m 1 i) (Q.comp m 1 i) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair, whiskerLeft_comp, Category.assoc]
  rw [tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, P.comp_unit, Q.comp_unit]
  exact (tensor_right_unitality (P.arity (m + 1)) (Q.arity (m + 1))).symm


/-- 概要：Hadamard 積の内側等変性（Berger–Moerdijk §1）。
方針：tensorμ の右自然性の後で各列の等変性を使う。
規約：置換は挿入区間でのみ作用する。
使われ方：Hadamard オペラッドの対称性の公理となる。 -/
lemma inner_equivariance (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (i : Fin (m + 1))
    (τ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) (m + 1) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q).map (_root_.SerrePositivity.FiniteBijection.permutation n τ)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m n i =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m n i ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q).map
      (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ)) := by
  change (_ ◁ (_ ⊗ₘ _)) ≫ (tensorμ _ _ _ _ ≫ _) =
    (tensorμ _ _ _ _ ≫ _) ≫ (_ ⊗ₘ _)
  rw [← Category.assoc, tensorμ_natural_right]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  exact congrArg (fun f => tensorμ (P.arity (m + 1)) (Q.arity (m + 1))
    (P.arity n) (Q.arity n) ≫ f)
      (congrArg₂ (fun f g => f ⊗ₘ g) (P.inner_equivariance m n i τ)
        (Q.inner_equivariance m n i τ))

/-- 概要：Hadamard 積の外側等変性（Berger–Moerdijk §1）。
方針：tensorμ の左自然性の後で各列の等変性を使う。
規約：代入位置は外側の置換に沿って移動する。
使われ方：Hadamard オペラッドの対称性の公理となる。 -/
lemma outer_equivariance (P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q).map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ▷
      _root_.SerrePositivity.SymmetricSequence.level (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q) n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m n (σ i) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.comp P Q m n i ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.sequence P Q).map
      (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)) := by
  change ((_ ⊗ₘ _) ▷ _) ≫ (tensorμ _ _ _ _ ≫ _) =
    (tensorμ _ _ _ _ ≫ _) ≫ (_ ⊗ₘ _)
  rw [← Category.assoc, tensorμ_natural_left]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  exact congrArg (fun f => tensorμ (P.arity (m + 1)) (Q.arity (m + 1))
    (P.arity n) (Q.arity n) ≫ f)
      (congrArg₂ (fun f g => f ⊗ₘ g) (P.outer_equivariance m n i σ)
        (Q.outer_equivariance m n i σ))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard
