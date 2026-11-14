module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.HomotopyEndpointComparison

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.IntervalEndpoints

/-!
# 中断した任意モデル源への一般化：RetractChainFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All finite chains with independently prescribed contraction parameters。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0547][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0547
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All finite chains with independently prescribed contraction parameters

Every junction has a parameter map into the interval. The zero face merges
adjacent actual arrows; the one face splits the transferred family. Both
formulas hold inside arbitrary finite prefixes and suffixes, and commute
with arbitrary parameter substitution. No model structure is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RetractChainFamily
variable {ι : Type u} (E : ι → SSet.{v})

inductive Chain (T : SSet.{v}) (a : ι) : ι → Type (max u (v + 1))
  | nil : Chain T a a
  | familySnoc {b c : ι} (p : Chain T a b)
      (f : E b ⊗ T ⟶ E c) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) : Chain T a c

namespace Chain
variable {E} {T U : SSet.{v}} {a b c d : ι}

def snoc (q : Chain E T a b) (f : E b ⟶ E c) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) : Chain E T a c :=
  q.familySnoc (ParameterComposition.const T f) t

def length {a : ι} : {b : ι} → Chain E T a b → ℕ
  | _, .nil => 0
  | _, .familySnoc p _ _ => p.length + 1

def append (p : Chain E T a b) : {c : ι} → Chain E T b c → Chain E T a c
  | _, .nil => p
  | _, .familySnoc q f t => .familySnoc (append p q) f t

def substitute (j : U ⟶ T) {a : ι} : {b : ι} → Chain E T a b → Chain E U a b
  | _, .nil => .nil
  | _, .familySnoc p f t =>
      .familySnoc (substitute j p) (ParameterComposition.substitute j f) (j ≫ t)

def sequence (b : ℕ → ι) (f : ∀ n, E (b n) ⟶ E (b (n + 1)))
    (t : ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) : ∀ n, Chain E T (b 0) (b n)
  | 0 => .nil
  | n + 1 => .snoc (sequence b f t n) (f n) (t n)

lemma sequence_length (b : ℕ → ι) (f : ∀ n, E (b n) ⟶ E (b (n + 1)))
    (t : ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) (n : ℕ) : (sequence b f t n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => change (sequence b f t n).length + 1 = n + 1; rw [ih]

lemma substitute_sequence (j : U ⟶ T) (b : ℕ → ι)
    (f : ∀ n, E (b n) ⟶ E (b (n + 1))) (t : ℕ → (T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)) (n : ℕ) :
    (sequence b f t n).substitute j = sequence b f (fun k => j ≫ t k) n := by
  induction n with
  | zero => rfl
  | succ n ih => change (substitute j (sequence b f t n)).snoc _ _ = _; rw [ih]; rfl

end Chain

variable (K : ι → SSet.{v}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
  (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))

def contraction (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) : E i ⊗ T ⟶ E i :=
  E i ◁ t ≫ (H i).h

lemma contraction_zero (i : ι) (T : SSet.{v}) :
    contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T) = ParameterComposition.const T (𝟙 (E i)) := by
  rw [contraction, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero, whiskerLeft_comp, Category.assoc,
    HomotopyEndpointComparison.face_zero]
  ext n x
  rfl

lemma contraction_one (i : ι) (T : SSet.{v}) :
    contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T) = ParameterComposition.const T (p i ≫ s i) := by
  rw [contraction, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one, whiskerLeft_comp, Category.assoc,
    HomotopyEndpointComparison.face_one]
  ext n x
  rfl

lemma contraction_substitute (i : ι) {T U : SSet.{v}} (j : U ⟶ T) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    contraction E K s p H i (j ≫ t) =
      ParameterComposition.substitute j (contraction E K s p H i t) := by
  rw [contraction, contraction, ParameterComposition.substitute, whiskerLeft_comp, Category.assoc]

def evaluate {T : SSet.{v}} {a : ι} : {b : ι} → Chain E T a b → (E a ⊗ T ⟶ E b)
  | _, .nil => ParameterComposition.const T (𝟙 (E a))
  | _, .familySnoc q f t => ParameterComposition.comp (evaluate q)
      (ParameterComposition.comp f (contraction E K s p H _ t))

lemma evaluate_append {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (r : Chain E T b c) :
    evaluate E K s p H (q.append r) =
      ParameterComposition.comp (evaluate E K s p H q) (evaluate E K s p H r) := by
  induction r with
  | nil => exact (ParameterComposition.comp_id _).symm
  | familySnoc r f t ih =>
    change ParameterComposition.comp (evaluate E K s p H (q.append r)) _ = _
    rw [ih, ParameterComposition.assoc]
    rfl

lemma evaluate_substitute {T U : SSet.{v}} {a b : ι} (j : U ⟶ T) (q : Chain E T a b) :
    evaluate E K s p H (q.substitute j) =
      ParameterComposition.substitute j (evaluate E K s p H q) := by
  induction q with
  | nil => exact (ParameterComposition.substitute_const j _).symm
  | familySnoc q f t ih =>
    change ParameterComposition.comp (evaluate E K s p H (q.substitute j)) _ = _
    simp only [evaluate]
    rw [ih, ParameterComposition.substitute_comp, ParameterComposition.substitute_comp,
      ← contraction_substitute]

def transfer {T : SSet.{v}} {a b : ι} (q : Chain E T a b) : K a ⊗ T ⟶ K b :=
  ParameterComposition.comp (ParameterComposition.const T (s a))
    (ParameterComposition.comp (evaluate E K s p H q) (ParameterComposition.const T (p b)))

lemma transfer_substitute {T U : SSet.{v}} {a b : ι} (j : U ⟶ T) (q : Chain E T a b) :
    transfer E K s p H (q.substitute j) =
      ParameterComposition.substitute j (transfer E K s p H q) := by
  simp only [transfer, ParameterComposition.substitute_comp,
    ParameterComposition.substitute_const, evaluate_substitute]

lemma zero_family_face {T : SSet.{v}} {a b c d e : ι} (q : Chain E T a b)
    (f : E b ⊗ T ⟶ E c) (g : E c ⊗ T ⟶ E d) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval)
    (r : Chain E T d e) :
    transfer E K s p H (((q.familySnoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).familySnoc g t).append r) =
      transfer E K s p H ((q.familySnoc (ParameterComposition.comp f g) t).append r) := by
  have he : evaluate E K s p H ((q.familySnoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).familySnoc g t) =
      evaluate E K s p H (q.familySnoc (ParameterComposition.comp f g) t) := by
    simp only [evaluate, contraction_zero, ParameterComposition.comp_id]
    ext n x
    rfl
  simp only [transfer, evaluate_append, he]

lemma transfer_last_family_parameter
    (hH : ∀ i, (H i).h ≫ p i = fst (E i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ p i)
    {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (f : E b ⊗ T ⟶ E c)
    (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    transfer E K s p H (q.familySnoc f t) =
      ParameterComposition.comp (ParameterComposition.const T (s a))
        (ParameterComposition.comp (evaluate E K s p H q)
          (ParameterComposition.comp f (ParameterComposition.const T (p c)))) := by
  have he : ParameterComposition.comp (contraction E K s p H c t)
      (ParameterComposition.const T (p c)) = ParameterComposition.const T (p c) := by
    rw [ParameterComposition.comp_const, contraction, Category.assoc, hH]
    ext n x
    rfl
  simp only [transfer, evaluate, ParameterComposition.assoc, he]

lemma one_family_face
    (hH : ∀ i, (H i).h ≫ p i = fst (E i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ p i)
    {T : SSet.{v}} {a b c d : ι} (q : Chain E T a b) (f : E b ⊗ T ⟶ E c)
    (r : Chain E T c d) :
    transfer E K s p H ((q.familySnoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)).append r) =
      ParameterComposition.comp (transfer E K s p H (q.familySnoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)))
        (transfer E K s p H r) := by
  rw [transfer_last_family_parameter E K s p H hH]
  simp only [transfer, evaluate_append, evaluate, contraction_one]
  ext n x
  rfl

lemma zero_face {T : SSet.{v}} {a b c d e : ι} (q : Chain E T a b)
    (f : E b ⟶ E c) (g : E c ⟶ E d) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) (r : Chain E T d e) :
    transfer E K s p H (((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).snoc g t).append r) =
      transfer E K s p H ((q.snoc (f ≫ g) t).append r) := by
  simpa only [Chain.snoc, ParameterComposition.const_comp] using
    zero_family_face E K s p H q (ParameterComposition.const T f)
      (ParameterComposition.const T g) t r

lemma transfer_last_parameter
    (hH : ∀ i, (H i).h ≫ p i = fst (E i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ p i)
    {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (f : E b ⟶ E c) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    transfer E K s p H (q.snoc f t) =
      ParameterComposition.comp (ParameterComposition.const T (s a))
        (ParameterComposition.comp (evaluate E K s p H q)
          (ParameterComposition.const T (f ≫ p c))) := by
  simpa only [Chain.snoc, ParameterComposition.const_comp] using
    transfer_last_family_parameter E K s p H hH q (ParameterComposition.const T f) t

lemma one_face
    (hH : ∀ i, (H i).h ≫ p i = fst (E i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ p i)
    {T : SSet.{v}} {a b c d : ι} (q : Chain E T a b) (f : E b ⟶ E c)
    (r : Chain E T c d) :
    transfer E K s p H ((q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)).append r) =
      ParameterComposition.comp (transfer E K s p H (q.snoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)))
        (transfer E K s p H r) := by
  simpa only [Chain.snoc] using
    one_family_face E K s p H hH q (ParameterComposition.const T f) r

end SerrePositivity.SimplicialModel.RetractChainFamily
