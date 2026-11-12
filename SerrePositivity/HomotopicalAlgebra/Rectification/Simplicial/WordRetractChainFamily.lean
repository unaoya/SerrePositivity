module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordRetractionAction

/-!
# 中断した任意モデル源への一般化：WordRetractChainFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Finite retract chains with word parameters and arbitrary internal unit elimination。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0615][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0615
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Finite retract chains with word parameters and arbitrary internal unit elimination

Every junction is parameterized by the actual word segment. Adjacent
contractions concatenate strictly, allowing an internal identity to be
removed with no endpoint restriction on either neighboring parameter.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.WordRetractChainFamily
variable {ι : Type u} (E : ι → SSet.{v})

inductive Chain (T : SSet.{v}) (a : ι) : ι → Type (max u (v + 1))
  | nil : Chain T a a
  | familySnoc {b c : ι} (p : Chain T a b)
      (f : E b ⊗ T ⟶ E c) (t : T ⟶ WordSegment.obj) : Chain T a c

namespace Chain
variable {E} {T U : SSet.{v}} {a b c d : ι}

def snoc (q : Chain E T a b) (f : E b ⟶ E c) (t : T ⟶ WordSegment.obj) : Chain E T a c :=
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
    (t : ℕ → (T ⟶ WordSegment.obj)) : ∀ n, Chain E T (b 0) (b n)
  | 0 => .nil
  | n + 1 => .snoc (sequence b f t n) (f n) (t n)

lemma sequence_length (b : ℕ → ι) (f : ∀ n, E (b n) ⟶ E (b (n + 1)))
    (t : ℕ → (T ⟶ WordSegment.obj)) (n : ℕ) : (sequence b f t n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => change (sequence b f t n).length + 1 = n + 1; rw [ih]

lemma substitute_sequence (j : U ⟶ T) (b : ℕ → ι)
    (f : ∀ n, E (b n) ⟶ E (b (n + 1))) (t : ℕ → (T ⟶ WordSegment.obj)) (n : ℕ) :
    (sequence b f t n).substitute j = sequence b f (fun k => j ≫ t k) n := by
  induction n with
  | zero => rfl
  | succ n ih => change (substitute j (sequence b f t n)).snoc _ _ = _; rw [ih]; rfl

def ofInterval {a : ι} : {b : ι} → RetractChainFamily.Chain E T a b → Chain E T a b
  | _, .nil => .nil
  | _, .familySnoc q f t => .familySnoc (ofInterval q) f (t ≫ WordSegment.letter)

lemma ofInterval_substitute (j : U ⟶ T) {a b : ι} (q : RetractChainFamily.Chain E T a b) :
    ofInterval (q.substitute j) = (ofInterval q).substitute j := by
  induction q with
  | nil => rfl
  | familySnoc q f t ih =>
    change (ofInterval (q.substitute j)).familySnoc _ _ = _
    rw [ih]
    rfl

end Chain

variable (K : ι → SSet.{v}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
  (hs : ∀ i, s i ≫ p i = 𝟙 (K i))
  (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))
  (hP : ∀ i, (H i).h ≫ p i = fst (E i) WordSegment.interval ≫ p i)
  (hS : ∀ i, s i ▷ WordSegment.interval ≫ (H i).h =
    fst (K i) WordSegment.interval ≫ s i)

def contraction (i : ι) {T : SSet.{v}} (t : T ⟶ WordSegment.obj) : E i ⊗ T ⟶ E i :=
  E i ◁ t ≫ WordRetractionAction.action (s i) (p i) (hs i) (H i) (hP i) (hS i)

lemma contraction_unit (i : ι) (T : SSet.{v}) :
    contraction E K s p hs H hP hS i (WordSegment.unitAt T) =
      ParameterComposition.const T (𝟙 (E i)) := by
  ext n x
  change WordRetractionAction.eval (s i) (p i) (hs i) (H i) (hP i) (hS i) n 1 x.1 = x.1
  rw [map_one, RetractEndomorphisms.one_apply]

lemma contraction_zero (i : ι) (T : SSet.{v}) :
    contraction E K s p hs H hP hS i (WordSegment.zeroAt T) =
      ParameterComposition.const T (p i ≫ s i) := by
  ext n x
  change WordRetractionAction.eval (s i) (p i) (hs i) (H i) (hP i) (hS i) n 0 x.1 = _
  rw [map_zero, RetractEndomorphisms.zero_apply]
  rfl

lemma contraction_mul (i : ι) {T : SSet.{v}} (t w : T ⟶ WordSegment.obj) :
    ParameterComposition.comp (contraction E K s p hs H hP hS i t)
      (contraction E K s p hs H hP hS i w) =
        contraction E K s p hs H hP hS i (lift t w ≫ WordSegment.mul) := by
  ext n x
  change _ = WordRetractionAction.eval (s i) (p i) (hs i) (H i) (hP i) (hS i) n
    (t.app n x.2 * w.app n x.2) x.1
  rw [map_mul]
  rfl

lemma contraction_substitute (i : ι) {T U : SSet.{v}} (j : U ⟶ T) (t : T ⟶ WordSegment.obj) :
    contraction E K s p hs H hP hS i (j ≫ t) =
      ParameterComposition.substitute j (contraction E K s p hs H hP hS i t) := by
  rw [contraction, contraction, ParameterComposition.substitute,
    whiskerLeft_comp, Category.assoc]

def evaluate {T : SSet.{v}} {a : ι} : {b : ι} → Chain E T a b → (E a ⊗ T ⟶ E b)
  | _, .nil => ParameterComposition.const T (𝟙 (E a))
  | _, .familySnoc q f t => ParameterComposition.comp (evaluate q)
      (ParameterComposition.comp f (contraction E K s p hs H hP hS _ t))

lemma evaluate_append {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (r : Chain E T b c) :
    evaluate E K s p hs H hP hS (q.append r) =
      ParameterComposition.comp (evaluate E K s p hs H hP hS q)
        (evaluate E K s p hs H hP hS r) := by
  induction r with
  | nil => exact (ParameterComposition.comp_id _).symm
  | familySnoc r f t ih =>
    change ParameterComposition.comp (evaluate E K s p hs H hP hS (q.append r)) _ = _
    rw [ih, ParameterComposition.assoc]
    rfl

lemma evaluate_substitute {T U : SSet.{v}} {a b : ι} (j : U ⟶ T) (q : Chain E T a b) :
    evaluate E K s p hs H hP hS (q.substitute j) =
      ParameterComposition.substitute j (evaluate E K s p hs H hP hS q) := by
  induction q with
  | nil => exact (ParameterComposition.substitute_const j _).symm
  | familySnoc q f t ih =>
    change ParameterComposition.comp (evaluate E K s p hs H hP hS (q.substitute j)) _ = _
    simp only [evaluate]
    rw [ih, ParameterComposition.substitute_comp, ParameterComposition.substitute_comp,
      ← contraction_substitute]

def transfer {T : SSet.{v}} {a b : ι} (q : Chain E T a b) : K a ⊗ T ⟶ K b :=
  ParameterComposition.comp (ParameterComposition.const T (s a))
    (ParameterComposition.comp (evaluate E K s p hs H hP hS q)
      (ParameterComposition.const T (p b)))

lemma transfer_substitute {T U : SSet.{v}} {a b : ι} (j : U ⟶ T) (q : Chain E T a b) :
    transfer E K s p hs H hP hS (q.substitute j) =
      ParameterComposition.substitute j (transfer E K s p hs H hP hS q) := by
  simp only [transfer, ParameterComposition.substitute_comp,
    ParameterComposition.substitute_const, evaluate_substitute]

lemma unit_family_face {T : SSet.{v}} {a b c d e : ι} (q : Chain E T a b)
    (f : E b ⊗ T ⟶ E c) (g : E c ⊗ T ⟶ E d) (t : T ⟶ WordSegment.obj)
    (r : Chain E T d e) :
    transfer E K s p hs H hP hS
      (((q.familySnoc f (WordSegment.unitAt T)).familySnoc g t).append r) =
      transfer E K s p hs H hP hS ((q.familySnoc (ParameterComposition.comp f g) t).append r) := by
  have he : evaluate E K s p hs H hP hS ((q.familySnoc f (WordSegment.unitAt T)).familySnoc g t) =
      evaluate E K s p hs H hP hS (q.familySnoc (ParameterComposition.comp f g) t) := by
    simp only [evaluate, contraction_unit, ParameterComposition.comp_id]
    ext n x
    rfl
  simp only [transfer, evaluate_append, he]

lemma transfer_last_family_parameter
    {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (f : E b ⊗ T ⟶ E c)
    (t : T ⟶ WordSegment.obj) :
    transfer E K s p hs H hP hS (q.familySnoc f t) =
      ParameterComposition.comp (ParameterComposition.const T (s a))
        (ParameterComposition.comp (evaluate E K s p hs H hP hS q)
          (ParameterComposition.comp f (ParameterComposition.const T (p c)))) := by
  have he : ParameterComposition.comp (contraction E K s p hs H hP hS c t)
      (ParameterComposition.const T (p c)) = ParameterComposition.const T (p c) := by
    rw [ParameterComposition.comp_const, contraction, Category.assoc,
      WordRetractionAction.action_over]
    ext n x
    rfl
  simp only [transfer, evaluate, ParameterComposition.assoc, he]

lemma zero_family_face
    {T : SSet.{v}} {a b c d : ι} (q : Chain E T a b) (f : E b ⊗ T ⟶ E c)
    (r : Chain E T c d) :
    transfer E K s p hs H hP hS ((q.familySnoc f (WordSegment.zeroAt T)).append r) =
      ParameterComposition.comp
        (transfer E K s p hs H hP hS (q.familySnoc f (WordSegment.unitAt T)))
        (transfer E K s p hs H hP hS r) := by
  rw [transfer_last_family_parameter E K s p hs H hP hS]
  simp only [transfer, evaluate_append, evaluate, contraction_zero]
  ext n x
  rfl

lemma unit_face {T : SSet.{v}} {a b c d e : ι} (q : Chain E T a b)
    (f : E b ⟶ E c) (g : E c ⟶ E d) (t : T ⟶ WordSegment.obj) (r : Chain E T d e) :
    transfer E K s p hs H hP hS (((q.snoc f (WordSegment.unitAt T)).snoc g t).append r) =
      transfer E K s p hs H hP hS ((q.snoc (f ≫ g) t).append r) := by
  simpa only [Chain.snoc, ParameterComposition.const_comp] using
    unit_family_face E K s p hs H hP hS q (ParameterComposition.const T f)
      (ParameterComposition.const T g) t r

lemma transfer_last_parameter
    {T : SSet.{v}} {a b c : ι} (q : Chain E T a b) (f : E b ⟶ E c) (t : T ⟶ WordSegment.obj) :
    transfer E K s p hs H hP hS (q.snoc f t) =
      ParameterComposition.comp (ParameterComposition.const T (s a))
        (ParameterComposition.comp (evaluate E K s p hs H hP hS q)
          (ParameterComposition.const T (f ≫ p c))) := by
  simpa only [Chain.snoc, ParameterComposition.const_comp] using
    transfer_last_family_parameter E K s p hs H hP hS q (ParameterComposition.const T f) t

lemma zero_face
    {T : SSet.{v}} {a b c d : ι} (q : Chain E T a b) (f : E b ⟶ E c)
    (r : Chain E T c d) :
    transfer E K s p hs H hP hS ((q.snoc f (WordSegment.zeroAt T)).append r) =
      ParameterComposition.comp (transfer E K s p hs H hP hS (q.snoc f (WordSegment.unitAt T)))
        (transfer E K s p hs H hP hS r) := by
  simpa only [Chain.snoc] using
    zero_family_face E K s p hs H hP hS q (ParameterComposition.const T f) r

lemma interior_identity {T : SSet.{v}} {a b c d : ι}
    (q : Chain E T a b) (f : E b ⊗ T ⟶ E c) (t w : T ⟶ WordSegment.obj)
    (r : Chain E T c d) :
    transfer E K s p hs H hP hS
      (((q.familySnoc f t).familySnoc (ParameterComposition.const T (𝟙 (E c))) w).append r) =
      transfer E K s p hs H hP hS
        ((q.familySnoc f (lift t w ≫ WordSegment.mul)).append r) := by
  have he : evaluate E K s p hs H hP hS
      ((q.familySnoc f t).familySnoc (ParameterComposition.const T (𝟙 (E c))) w) =
      evaluate E K s p hs H hP hS (q.familySnoc f (lift t w ≫ WordSegment.mul)) := by
    simp only [evaluate, ParameterComposition.id_comp, ParameterComposition.assoc]
    rw [contraction_mul]
  simp only [transfer, evaluate_append, he]

lemma trailing_identity {T : SSet.{v}} {a b : ι}
    (q : Chain E T a b) (t : T ⟶ WordSegment.obj) :
    transfer E K s p hs H hP hS
      (q.familySnoc (ParameterComposition.const T (𝟙 (E b))) t) =
      transfer E K s p hs H hP hS q := by
  rw [transfer_last_family_parameter, ParameterComposition.id_comp]
  rfl

lemma section_comp_contraction (i : ι) {T : SSet.{v}} (t : T ⟶ WordSegment.obj) :
    ParameterComposition.comp (ParameterComposition.const T (s i))
      (contraction E K s p hs H hP hS i t) = ParameterComposition.const T (s i) := by
  ext n x
  exact (WordRetractionAction.eval (s i) (p i) (hs i) (H i) (hP i) (hS i) n
    (t.app n x.2)).fixed x.1

lemma leading_identity {T : SSet.{v}} {a b : ι}
    (q : Chain E T a b) (t : T ⟶ WordSegment.obj) :
    transfer E K s p hs H hP hS
      (((Chain.nil : Chain E T a a).familySnoc
        (ParameterComposition.const T (𝟙 (E a))) t).append q) =
      transfer E K s p hs H hP hS q := by
  simp only [transfer, evaluate_append, evaluate, ParameterComposition.id_comp,
    ParameterComposition.assoc]
  rw [← ParameterComposition.assoc, section_comp_contraction]

lemma contraction_letter (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    contraction E K s p hs H hP hS i (t ≫ WordSegment.letter) =
      RetractChainFamily.contraction E K s p H i t := by
  rw [contraction, whiskerLeft_comp, Category.assoc, WordRetractionAction.action_letter]
  rfl

lemma evaluate_ofInterval {T : SSet.{v}} {a b : ι} (q : RetractChainFamily.Chain E T a b) :
    evaluate E K s p hs H hP hS (Chain.ofInterval q) =
      RetractChainFamily.evaluate E K s p H q := by
  induction q with
  | nil => rfl
  | familySnoc q f t ih =>
    change ParameterComposition.comp (evaluate E K s p hs H hP hS (Chain.ofInterval q)) _ = _
    rw [ih, contraction_letter]
    rfl

lemma transfer_ofInterval {T : SSet.{v}} {a b : ι} (q : RetractChainFamily.Chain E T a b) :
    transfer E K s p hs H hP hS (Chain.ofInterval q) =
      RetractChainFamily.transfer E K s p H q := by
  unfold transfer RetractChainFamily.transfer
  rw [evaluate_ofInterval]

end SerrePositivity.SimplicialModel.WordRetractChainFamily
