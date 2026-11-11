module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedNaturality

/-! # 線形方程式の解の引き戻し

概要：線形成分族の引き戻しを解の部分加群へ制限し、A 線形写像とする。
方針：実際の単体の引き戻しと成分回収の自然性から解であることを得る。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：実際の写像空間の線形な面・退化。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

namespace LinearSimplex

/-- 概要：線形族の引き戻しは線形方程式の解を解に送る。
方針：逆構成した実際の単体を引き戻して回収し、自然性と逆則を適用する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：解の部分加群への引き戻しの制限。 -/
lemma pullback_mem {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f.val ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearSubmodule A x y m := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (f.toPinched.pullback (SimplexCategory.mkHom α))).property
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (f.toPinched.pullback (SimplexCategory.mkHom α)) ∈ _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_pullback] at h
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData f.toPinched = f.val := congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched f)
  rw [he] at h
  exact h

/-- 概要：線形方程式の解の引き戻しは A 線形写像。
方針：成分族の線形写像を解の部分加群へ制限する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形模型の全ての面と退化。 -/
def pullback {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n →ₗ[A] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y m where
  toFun f := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f.val, pullback_mem α f⟩
  map_add' f g := Subtype.ext (map_add (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α) f.val g.val)
  map_smul' c f := Subtype.ext (map_smul (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α) c f.val)

/-- 概要：解の引き戻しの台の成分族は元の線形引き戻し。
方針：部分加群への制限の定義を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：成分の計算。 -/
lemma pullback_val {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    (pullback α f).val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α f.val := rfl

/-- 概要：解の引き戻しは恒等写像を保つ。
方針：成分族の恒等則と部分加群の外延性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的恒等則。 -/
lemma pullback_id {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) : pullback OrderHom.id f = f :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_id f.val)

/-- 概要：解の引き戻しは反変に合成する。
方針：成分族の合成則と部分加群の外延性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的合成則。 -/
lemma pullback_comp {l m n : ℕ} (α : Fin (l + 1) →o Fin (m + 1))
    (β : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A x y n) :
    pullback α (pullback β f) = pullback (β.comp α) f :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_comp α β f.val)

end LinearSimplex

/-- 概要：実際の単体と線形解の比較は全引き戻しと可換。
方針：成分回収の自然性と解の部分加群の外延性を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：全次数の同値の単体的な自然性。 -/
lemma toLinearSimplex_pullback {m n : SimplexCategory}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n.len⦌) (α : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (s.pullback α) = LinearSimplex.pullback α.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s) :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_pullback s α)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
