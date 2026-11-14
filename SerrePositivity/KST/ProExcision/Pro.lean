module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

@[expose] public section

/-!
# ℕ 添字の最小 pro 形式

概要：塔とレベル射を使い Artin–Mazur 型の pro 同型判定を記述する。
方針：一般の pro 圏を作らず、遷移射による二つの三角形を用いる。
規約：遷移は大きい添字から小さい添字へ向かう。
使われ方：KST §4.1、Definition 4.4・Lemma 4.6 と正本 §2.6 の L3・L4。
-/

universe u v u' v'

namespace SerrePositivity.KST.ProExcision

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- 概要：ℕ 添字の逆系。方針：全順序射を明示する。
規約：`transition h` は大きい添字から小さい添字への射。
使われ方：KST §4.1 の pro 対象の最小形式。 -/
structure Tower where
  obj : ℕ → C
  transition : {m n : ℕ} → n ≤ m → (obj m ⟶ obj n)
  transition_self : ∀ n, transition (le_refl n) = 𝟙 (obj n)
  transition_comp : ∀ {k m n} (hm : m ≤ k) (hn : n ≤ m),
    transition hm ≫ transition hn = transition (hn.trans hm)

variable {C}

/-- 概要：同じ添字を持つ塔のレベル射。方針：各遷移との可換性を持たせる。
規約：`app n` は n 段の射。使われ方：KST §4.1 の strict morphism。 -/
structure LevelHom (X Y : Tower C) where
  app : ∀ n, X.obj n ⟶ Y.obj n
  naturality : ∀ {m n} (h : n ≤ m),
    X.transition h ≫ app n = app m ≫ Y.transition h

/-- 概要：Artin–Mazur 型 pro 同型判定。方針：各段に eventual な逆射を要求する。
規約：逆射の族に自然性は要求せず二つの三角形を要求する。
使われ方：KST §4.1、正本 §2.6 の最小定義。 -/
def IsProIso {X Y : Tower C} (f : LevelHom X Y) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, ∃ g : Y.obj m ⟶ X.obj n,
    f.app m ≫ g = X.transition h ∧ g ≫ f.app n = Y.transition h

namespace Tower

/-- 概要：定数塔。方針：遷移を恒等射とする。
規約：全段が同じ対象。使われ方：KST §4.1 の定数 pro 対象。 -/
def constant (A : C) : Tower C where
  obj _ := A
  transition _ := 𝟙 A
  transition_self _ := rfl
  transition_comp _ _ := Category.id_comp _

variable {D : Type u'} [Category.{v'} D]

/-- 概要：関手による塔の像。方針：対象と遷移射を写す。
規約：添字は変更しない。使われ方：正本 §2.6 L3、有理テンソルへの適用。 -/
def map (X : Tower C) (F : C ⥤ D) : Tower D where
  obj n := F.obj (X.obj n)
  transition h := F.map (X.transition h)
  transition_self n := by rw [X.transition_self, F.map_id]
  transition_comp hm hn := by rw [← F.map_comp, X.transition_comp]

end Tower

namespace LevelHom

/-- 概要：塔の恒等レベル射。方針：各段で恒等射を使う。
規約：自然性は単位律。使われ方：pro 同型の反射性。 -/
def id (X : Tower C) : LevelHom X X where
  app n := 𝟙 (X.obj n)
  naturality _ := by simp

/-- 概要：レベル射の合成。方針：各段で合成する。
規約：f の後に g を適用。使われ方：pro 同型の推移性。 -/
def comp {X Y Z : Tower C} (f : LevelHom X Y) (g : LevelHom Y Z) : LevelHom X Z where
  app n := f.app n ≫ g.app n
  naturality h := by rw [← Category.assoc, f.naturality h,
    Category.assoc, g.naturality h, ← Category.assoc]

variable {D : Type u'} [Category.{v'} D]

/-- 概要：関手によるレベル射の像。方針：可換な四角形を関手で写す。
規約：元の添字を保つ。使われ方：正本 §2.6 L3。 -/
def map {X Y : Tower C} (f : LevelHom X Y) (F : C ⥤ D) :
    LevelHom (X.map F) (Y.map F) where
  app n := F.map (f.app n)
  naturality h := by
    change F.map (X.transition h) ≫ F.map (f.app _) =
      F.map (f.app _) ≫ F.map (Y.transition h)
    rw [← F.map_comp, f.naturality, F.map_comp]

end LevelHom

namespace IsProIso

/-- 概要：恒等射は pro 同型。方針：同じ段で逆射を選ぶ。
規約：添字を進める必要はない。使われ方：KST §4.1 の判定の基本性質。 -/
theorem id (X : Tower C) : IsProIso (LevelHom.id X) := by
  intro n
  refine ⟨n, le_refl n, 𝟙 (X.obj n), ?_, ?_⟩ <;>
    simp [LevelHom.id, X.transition_self]

/-- 概要：任意の関手は pro 同型判定を保存する。
方針：逆射と二つの三角形を関手で写す。
規約：加法性や完全性は不要。使われ方：正本 §2.6 L3、⊗ℚ の pro 同型保存。 -/
theorem map {D : Type u'} [Category.{v'} D] {X Y : Tower C}
    {f : LevelHom X Y} (hf : IsProIso f) (F : C ⥤ D) : IsProIso (f.map F) := by
  intro n
  obtain ⟨m, h, g, hg, gh⟩ := hf n
  refine ⟨m, h, F.map g, ?_, ?_⟩
  · change F.map (f.app m) ≫ F.map g = F.map (X.transition h)
    rw [← F.map_comp, hg]
  · change F.map g ≫ F.map (f.app n) = F.map (Y.transition h)
    rw [← F.map_comp, gh]

/-- 概要：pro 同型の合成も pro 同型。方針：二段の逆射を順に合成する。
規約：逆射の自然性は用いない。使われ方：KST §4.1 の比較射の連結。 -/
theorem comp {X Y Z : Tower C} {f : LevelHom X Y} {g : LevelHom Y Z}
    (hf : IsProIso f) (hg : IsProIso g) : IsProIso (f.comp g) := by
  intro n
  obtain ⟨m, hnm, a, ha, ah⟩ := hf n
  obtain ⟨k, hmk, b, hb, bh⟩ := hg m
  refine ⟨k, hnm.trans hmk, b ≫ a, ?_, ?_⟩
  · change (f.app k ≫ g.app k) ≫ (b ≫ a) = _
    rw [Category.assoc, ← Category.assoc (g.app k), hb,
      ← Category.assoc, ← f.naturality hmk, Category.assoc, ha, X.transition_comp]
  · change (b ≫ a) ≫ (f.app n ≫ g.app n) = _
    rw [Category.assoc, ← Category.assoc a, ah,
      g.naturality hnm, ← Category.assoc, bh, Z.transition_comp]

/-- 概要：定数塔間の pro 同型は元の射の逆射を与える。
方針：零段の判定を取り出す。規約：同一の射を全段で使う。
使われ方：KST Thm A から実際の降下へ移る定数塔の議論。 -/
theorem constant_inverse {A B : C} (f : A ⟶ B)
    (hf : IsProIso (X := Tower.constant A) (Y := Tower.constant B)
      { app := fun _ ↦ f, naturality := fun _ ↦ by simp [Tower.constant] }) :
    ∃ g : B ⟶ A, f ≫ g = 𝟙 A ∧ g ≫ f = 𝟙 B := by
  obtain ⟨_, _, g, hg, gh⟩ := hf 0
  exact ⟨g, hg, gh⟩

end IsProIso

/-- 概要：ℕ×ℕ の対角は共終。方針：二成分の最大値を選ぶ。
規約：上向きの共終性で逆系を再添字する。
使われ方：正本 §2.6 L4、KST Lemma 4.7 の対角化。 -/
theorem diagonal_cofinal (p : ℕ × ℕ) : ∃ n : ℕ, p ≤ (n, n) :=
  ⟨max p.1 p.2, le_max_left _ _, le_max_right _ _⟩

namespace Tower

/-- 概要：単調写像で塔を再添字する。方針：元の遷移を単調性で引き戻す。
規約：再添字後も ℕ 添字。使われ方：KST §4 の冪の塔の比較。 -/
def reindex (X : Tower C) (r : ℕ → ℕ) (hr : Monotone r) : Tower C where
  obj n := X.obj (r n)
  transition h := X.transition (hr h)
  transition_self n := X.transition_self (r n)
  transition_comp hm hn := X.transition_comp (hr hm) (hr hn)

/-- 概要：添字を進めた塔から元の塔への比較。
方針：r n ≥ n の遷移を用いる。規約：自然性は遷移の合成律。
使われ方：KST §4 の共終再添字。 -/
def reindexHom (X : Tower C) (r : ℕ → ℕ) (hr : Monotone r)
    (he : ∀ n, n ≤ r n) : LevelHom (X.reindex r hr) X where
  app n := X.transition (he n)
  naturality h := by
    change X.transition (hr h) ≫ X.transition (he _) =
      X.transition (he _) ≫ X.transition h
    rw [X.transition_comp, X.transition_comp]

/-- 概要：添字を進める単調再添字の比較は pro 同型。
方針：m = r n において恒等射を逆射に選ぶ。
規約：指数増大による共終性の十分条件。使われ方：KST §4 の塔の比較。 -/
theorem reindexHom_isProIso (X : Tower C) (r : ℕ → ℕ) (hr : Monotone r)
    (he : ∀ n, n ≤ r n) : IsProIso (X.reindexHom r hr he) := by
  intro n
  refine ⟨r n, he n, 𝟙 (X.obj (r n)), ?_, ?_⟩
  · change X.transition (he (r n)) ≫ 𝟙 _ = X.transition (hr (he n))
    simp
  · change 𝟙 _ ≫ X.transition (he n) = X.transition (he n)
    simp

end Tower

open CategoryTheory.Limits

/-- 概要：塔の pro-零性。方針：各段へ入る遷移の eventual な零化を要求する。
規約：零化指数は標的段に依存してよい。使われ方：KST Lemma 4.9・4.10。 -/
def IsProZero [HasZeroMorphisms C] (X : Tower C) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, X.transition h = 0

namespace IsProZero

/-- 概要：各段が同型なレベル射は pro-零性を移す。
方針：自然性の四角形と各段の同型で遷移を比較する。
規約：零化指数を変える必要はない。使われ方：KST Lemma 4.9 のモデル間比較。 -/
theorem of_levelwiseIso [HasZeroMorphisms C] {X Y : Tower C}
    (f : LevelHom X Y) [∀ n, IsIso (f.app n)] (hX : IsProZero X) : IsProZero Y := by
  intro n
  obtain ⟨m, h, hz⟩ := hX n
  refine ⟨m, h, ?_⟩
  rw [← cancel_epi (f.app m), ← f.naturality h, hz, zero_comp, comp_zero]

/-- 概要：零射を保つ関手は pro-零性を保つ。
方針：零化遷移を写す。規約：零射保存は明示的な引数。
使われ方：KST Lemma 4.9 の平坦係数への移行。 -/
theorem map {D : Type u'} [Category.{v'} D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] {X : Tower C} (hX : IsProZero X) (F : C ⥤ D)
    (hF : ∀ {A B : C}, F.map (0 : A ⟶ B) = 0) : IsProZero (X.map F) := by
  intro n
  obtain ⟨m, h, hz⟩ := hX n
  refine ⟨m, h, ?_⟩
  change F.map (X.transition h) = 0
  rw [hz, hF]

/-- 概要：添字を進める単調再添字は pro-零性を保つ。
方針：元の零化段より後へ進む。規約：添字増大を明示する。
使われ方：KST Lemma 4.9 の指数選択。 -/
theorem reindex [HasZeroMorphisms C] {X : Tower C} (hX : IsProZero X)
    (r : ℕ → ℕ) (hr : Monotone r) (he : ∀ n, n ≤ r n) :
    IsProZero (X.reindex r hr) := by
  intro n
  obtain ⟨m, h, hz⟩ := hX (r n)
  have hnm : n ≤ m := (he n).trans h
  refine ⟨m, hnm, ?_⟩
  change X.transition (hr hnm) = 0
  rw [← X.transition_comp (he m) h, hz, comp_zero]

end IsProZero

/-- 概要：次数別検出関手による pro 同値。
方針：各次数において Artin–Mazur 判定を使う。
規約：π_n 自体の構成は K-L9 から借りる。
使われ方：KST Definition 4.4 のスペクトルの pro 同値。 -/
def IsProEquivalence {D : Type u'} [Category.{v'} D] {ι : Type*}
    (invariants : ι → C ⥤ D) {X Y : Tower C} (f : LevelHom X Y) : Prop :=
  ∀ i, IsProIso (f.map (invariants i))

/-- 概要：レベルで形成した二つの hofib の比較による pro-cartesian 条件。
方針：与えられた fiber 比較の次数別 pro 同値を要求する。
規約：各レベルの比較が個別に同値であるとは要求しない。
使われ方：KST Lemma 4.6。fiber と比較射の構成は K-L9 の界面から受け取る。 -/
def IsProCartesian {D : Type u'} [Category.{v'} D] {ι : Type*}
    (invariants : ι → C ⥤ D) {F F' : Tower C}
    (fiberComparison : LevelHom F' F) : Prop :=
  IsProEquivalence invariants fiberComparison

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Def 4.4" (partial := component) "仮定：自然数添字と次数別のレベル図式・比較を使う（Lean が強い）。結論：次数別プロ同型による判定の抽象模型。スペクトルのホモトピー引き戻しと結ぶ比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.IsProCartesian
attribute [cite KST "Def 4.4" (partial := component) "仮定：自然数添字と次数別のレベル図式・比較を使う（Lean が強い）。結論：次数別プロ同型による判定の抽象模型。スペクトルのホモトピー引き戻しと結ぶ比較は含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.IsProEquivalence
attribute [cite KST "Eq (4.1)" (partial := component) "仮定：自然数塔と次数別の検出関手（Lean が強い）。結論：全ての指定検出関手でプロ同型を要求する定義。点付き空間とその π のプロ関手を実装した形はない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.IsProEquivalence
attribute [cite KST "Eq (4.2)" (partial := component) "仮定：次数別のレベル射でホモトピー比較を表す（Lean が強い）。結論：プロ引き戻しの判定条件を与える。任意のプロスペクトルの正方形そのものの型はない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.IsProCartesian
attribute [cite KST "Eq (4.3)" (partial := component) "仮定：自然数の二重添字の図式（Lean が強い）。結論：対角の共終性と、二重添字でプロ零の塔の対角のプロ零。各固定 m のスペクトル同値から二重添字全体への主張は別（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.diagonal_cofinal
attribute [cite KST "Lemma 4.6" (partial := component) "仮定：レベルのファイバー比較または既に与えたファイバー列（Lean が強い）。結論：比較がプロ同値であるという判定界面と、ファイバーのプロ連結度の群による比較。正方形の合成と実ホモトピー引き戻しの同値は供給しない（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.IsProCartesian
attribute [cite KST "Lemma 4.7" (partial := component) "仮定：自然数の二重添字の図式（Lean が強い）。結論：対角の共終性と、二重添字でプロ零の塔の対角のプロ零。各固定 m のスペクトル同値から二重添字全体への主張は別（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.diagonal_cofinal
