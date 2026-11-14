module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.Pro

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-!
# 独立な二つの冪指数と対角

概要：二つの添字を持つ逆系の行ごとの pro 同型を対角へ移す。
方針：標的段の行で得た逆射に、第一添字の遷移を前合成する。
規約：一般の pro 圏は導入せず、遷移の二つの三角形だけを使う。
使われ方：KST Lemma 4.9・4.10 の列長帰納法と §4.1 の対角共終性。
-/

universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable (C : Type u) [Category.{v} C]

/-- 概要：二つの独立な自然数を添字とする逆系。
方針：長方形の遷移とその合成則を指定する。
規約：両添字とも大きい段から小さい段へ向かう。
使われ方：KST Lemma 4.9・4.10 の独立な冪指数。 -/
structure BiTower where
  obj : ℕ → ℕ → C
  transition : {m n k l : ℕ} → n ≤ m → l ≤ k → (obj m k ⟶ obj n l)
  transition_self : ∀ m k, transition (le_refl m) (le_refl k) = 𝟙 (obj m k)
  transition_comp : ∀ {m n p k l q} (h₁ : n ≤ m) (h₂ : p ≤ n)
    (h₃ : l ≤ k) (h₄ : q ≤ l),
    transition h₁ h₃ ≫ transition h₂ h₄ = transition (h₂.trans h₁) (h₄.trans h₃)

variable {C}

/-- 概要：第一添字を固定した行の塔。
方針：第二添字の遷移を制限する。
規約：固定する段は任意。使われ方：KST Lemma 4.10 の一変数比較。 -/
def BiTower.row (X : BiTower C) (n : ℕ) : Tower C where
  obj k := X.obj n k
  transition h := X.transition (le_refl n) h
  transition_self k := X.transition_self n k
  transition_comp hm hn := X.transition_comp (le_refl n) (le_refl n) hm hn

/-- 概要：二重塔の対角の塔。
方針：二つの添字と遷移を同時に制限する。
規約：段 n は (n,n)。使われ方：KST Lemma 4.9・4.10 の通常の冪系への帰着。 -/
def BiTower.diagonal (X : BiTower C) : Tower C where
  obj n := X.obj n n
  transition h := X.transition h h
  transition_self n := X.transition_self n n
  transition_comp hm hn := X.transition_comp hm hn hm hn

/-- 概要：関手による二重塔の像。
方針：対象と全ての長方形遷移を関手で写す。
規約：添字は変えない。使われ方：KST Lemma 4.10 のホモロジーと通常商。 -/
def BiTower.map {D : Type*} [Category* D] (X : BiTower C) (F : C ⥤ D) : BiTower D where
  obj n k := F.obj (X.obj n k)
  transition h h' := F.map (X.transition h h')
  transition_self n k := by rw [X.transition_self, F.map_id]
  transition_comp h₁ h₂ h₃ h₄ := by rw [← F.map_comp, X.transition_comp]

/-- 概要：二重塔のレベル射。
方針：各長方形の遷移との自然性を指定する。
規約：両塔で同じ添字を使う。使われ方：KST Lemma 4.10 の二重冪比較。 -/
structure BiLevelHom (X Y : BiTower C) where
  app : ∀ n k, X.obj n k ⟶ Y.obj n k
  naturality : ∀ {m n k l} (h : n ≤ m) (h' : l ≤ k),
    X.transition h h' ≫ app n l = app m k ≫ Y.transition h h'

/-- 概要：二重塔の射を行へ制限する。
方針：第一添字を固定して自然性を使う。
規約：行番号は固定。使われ方：KST Lemma 4.10 の一変数ごとの pro 同型。 -/
def BiLevelHom.row {X Y : BiTower C} (f : BiLevelHom X Y) (n : ℕ) :
    LevelHom (X.row n) (Y.row n) where
  app k := f.app n k
  naturality h := f.naturality (le_refl n) h

/-- 概要：二重塔の射を対角へ制限する。
方針：両添字を同時に動かす自然性を使う。
規約：実際のレベル射。使われ方：KST Lemma 4.10 の単一の冪指数への帰着。 -/
def BiLevelHom.diagonal {X Y : BiTower C} (f : BiLevelHom X Y) :
    LevelHom X.diagonal Y.diagonal where
  app n := f.app n n
  naturality h := f.naturality h h

/-- 概要：各行が pro 同型なら、対角も pro 同型。
方針：n 行の n 段に対する eventual 逆射の前に第一添字の遷移を置く。
規約：行ごとの零化指数の一様性は不要。
使われ方：KST Lemma 4.10 の列長帰納法と KST §4.1 の独立添字。 -/
theorem BiLevelHom.diagonal_isProIso {X Y : BiTower C} (f : BiLevelHom X Y)
    (hf : ∀ n, IsProIso (f.row n)) : IsProIso f.diagonal := by
  intro n
  obtain ⟨m, h, g, hg, gh⟩ := hf n n
  change Y.obj n m ⟶ X.obj n n at g
  change f.app n m ≫ g = X.transition (le_refl n) h at hg
  change g ≫ f.app n n = Y.transition (le_refl n) h at gh
  refine ⟨m, h, Y.transition h (le_refl m) ≫ g, ?_, ?_⟩
  · change f.app m m ≫ Y.transition h (le_refl m) ≫ g = X.transition h h
    rw [← Category.assoc, ← f.naturality h (le_refl m), Category.assoc]
    rw [hg]
    exact X.transition_comp h (le_refl n) (le_refl m) h
  · change (Y.transition h (le_refl m) ≫ g) ≫ f.app n n = Y.transition h h
    rw [Category.assoc, gh]
    exact Y.transition_comp h (le_refl n) (le_refl m) h

/-- 概要：各行が pro-零なら対角も pro-零。
方針：n 行を零化し、対角からその行への遷移を前合成する。
規約：行番号に依存した指数を許す。
使われ方：KST Lemma 4.9 の固定された短い列に対する冪核の消滅。 -/
theorem BiTower.diagonal_isProZero [HasZeroMorphisms C] (X : BiTower C)
    (hX : ∀ n, IsProZero (X.row n)) : IsProZero X.diagonal := by
  intro n
  obtain ⟨m, h, hz⟩ := hX n n
  refine ⟨m, h, ?_⟩
  change X.transition h h = 0
  rw [← X.transition_comp h (le_refl n) (le_refl m) h]
  change X.transition h (le_refl m) ≫ (X.row n).transition h = 0
  rw [hz, comp_zero]

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Eq (4.3)" (partial := component) "仮定：自然数の二重添字の図式（Lean が強い）。結論：対角の共終性と、二重添字でプロ零の塔の対角のプロ零。各固定 m のスペクトル同値から二重添字全体への主張は別（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.BiTower.diagonal_isProZero
attribute [cite KST "Lemma 4.7" (partial := component) "仮定：自然数の二重添字の図式（Lean が強い）。結論：対角の共終性と、二重添字でプロ零の塔の対角のプロ零。各固定 m のスペクトル同値から二重添字全体への主張は別（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.BiTower.diagonal_isProZero
