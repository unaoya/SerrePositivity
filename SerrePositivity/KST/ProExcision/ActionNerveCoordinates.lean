module
public import SerrePositivity.KST.ProExcision.ActionCategory
public import SerrePositivity.KST.Comparison.BarSegal

/-!
# 作用圏の nerve の座標

概要：モノイド作用の nerve の単体を始点と射のラベルの列で記述する。
方針：始点を指定した射列を再帰的に構成し、射影のラベルと始点で一意性を示す。
規約：KST Proposition A.1 の作用 bar の行。射の合成は後のラベルが左。
使われ方：比較写像を G と H の有限積の作用の写像へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G X : Type u} [Monoid G] [MulAction G X]

/-- 概要：作用圏の合成のラベル。
方針：定義の積を評価する。
規約：KST Proposition A.1 の nerve の順序。使われ方：座標の一意性の証明。 -/
@[simp] lemma actionObject_comp_val {x y z : ActionObject G X} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = g.val * f.val := rfl

/-- 概要：作用圏の対象の等式からの射のラベルは単位。
方針：等式帰納法。
規約：KST Proposition A.1。使われ方：対象を同定した後の射のラベルの比較。 -/
@[simp] lemma actionObject_eqToHom_val {x y : ActionObject G X} (h : x = y) :
    (eqToHom h).val = (1 : G) := by cases h; rfl

/-- 概要：作用圏の nerve の始点と隣接ラベルの座標。
方針：始点を評価し、作用モノイドへの射影の Segal 座標を取る。
規約：KST Proposition A.1。使われ方：作用 bar の各行の積分解。 -/
def actionNerveCoordinates {n : ℕ} (p : (nerve (ActionObject G X)) _⦋n⦌) :
    X × (Fin n → G) :=
  ((p.obj 0).val, monoidWordLabels (MonCat.of G) (p ⋙ actionCategoryProjection))

/-- 概要：始点を指定した作用圏の射列を構成する。
方針：先頭ラベルで始点を移した射列へ帰納し、その前に先頭の射を付ける。
規約：KST Proposition A.1。構成と始点条件を一緒に保持する。
使われ方：作用 bar の座標の全射性。 -/
def actionNerveSimplexWithSource : (n : ℕ) → (x : X) → (Fin n → G) →
    {p : (nerve (ActionObject G X)) _⦋n⦌ // (p.obj 0).val = x}
  | 0, x, _ => ⟨ComposableArrows.mk₀ ⟨x⟩, rfl⟩
  | n + 1, x, g =>
    let p := actionNerveSimplexWithSource n (g 0 • x) (fun i ↦ g i.succ)
    ⟨p.val.precomp (show (⟨x⟩ : ActionObject G X) ⟶ p.val.left from
      ⟨g 0, p.property.symm⟩), rfl⟩

/-- 概要：作用圏の座標は単射。
方針：ラベルの射列の一致から全射のラベルを同定し、始点から各対象を同定する。
規約：KST Proposition A.1。逆元は不要。使われ方：作用 bar の有限積の一意性。 -/
lemma actionNerveCoordinates_injective (n : ℕ) :
    Function.Injective (actionNerveCoordinates (G := G) (X := X) (n := n)) := by
  intro p q h
  have h₀ : (p.obj 0).val = (q.obj 0).val := congrArg Prod.fst h
  have hl : p ⋙ actionCategoryProjection = q ⋙ actionCategoryProjection :=
    (monoidWordEquiv (MonCat.of G) n).injective (congrArg Prod.snd h)
  have hlabels {i j : Fin (n + 1)} (f : i ⟶ j) : (p.map f).val = (q.map f).val :=
    congrArg (fun a ↦ a.map f) hl
  have ho (i : Fin (n + 1)) : p.obj i = q.obj i := by
    apply ActionObject.ext
    have hp := (p.map (homOfLE (Fin.zero_le i))).property
    have hq := (q.map (homOfLE (Fin.zero_le i))).property
    rw [hlabels, h₀] at hp
    exact hp.symm.trans hq
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  apply Subtype.ext
  simp only [actionObject_comp_val, actionObject_eqToHom_val, mul_one, one_mul]
  exact hlabels f

/-- 概要：構成した射列の座標は指定した始点とラベル列に戻る。
方針：列の長さで帰納し、先頭と残りを分ける。
規約：KST Proposition A.1。使われ方：作用 bar の座標の全射性。 -/
lemma actionNerveCoordinates_simplex (n : ℕ) (x : X) (g : Fin n → G) :
    actionNerveCoordinates (actionNerveSimplexWithSource n x g).val = (x, g) := by
  apply Prod.ext
  · exact (actionNerveSimplexWithSource n x g).property
  · induction n generalizing x with
    | zero => exact funext (fun i ↦ Fin.elim0 i)
    | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · exact congrFun (ih (g 0 • x) (fun k ↦ g k.succ)) j

/-- 概要：作用圏の n 単体と始点×ラベルの列の全単射。
方針：明示した逆の全射性と座標の単射性を組み合わせる。
規約：KST Proposition A.1。使われ方：各行を有限積へ移す厳密同型。 -/
def actionNerveEquiv (n : ℕ) : (nerve (ActionObject G X)) _⦋n⦌ ≃ X × (Fin n → G) :=
  Equiv.ofBijective actionNerveCoordinates ⟨actionNerveCoordinates_injective n, by
    rintro ⟨x, g⟩
    exact ⟨(actionNerveSimplexWithSource n x g).val, actionNerveCoordinates_simplex n x g⟩⟩

/-- 概要：作用圏の始点とラベルの座標は同変な集合写像に自然。
方針：始点と隣接射のラベルを定義通り評価する。
規約：KST Proposition A.1。使われ方：各行の有限積の単体的同型。 -/
lemma actionNerveCoordinates_map {G' X' : Type u} [Monoid G'] [MulAction G' X']
    (f : G →* G') (g : X → X') (hg : ∀ a x, g (a • x) = f a • g x)
    {n : ℕ} (p : (nerve (ActionObject G X)) _⦋n⦌) :
    actionNerveCoordinates (p ⋙ actionCategoryMap f g hg) =
      (g (actionNerveCoordinates p).1, fun i ↦ f ((actionNerveCoordinates p).2 i)) := rfl

end SerrePositivity.KST.ProExcision
