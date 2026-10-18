module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
概要：関手圏の短複体の完全性を各対象で判定する。
方針：評価のコホモロジー比較と関手の零性の成分ごとの判定を使う。
規約：任意の小さい添字圏とアーベル圏。
使われ方：Stacks Lemma 19.12.4・Theorem 19.12.6、TT §3・§8、Toën §3.2 の非有界分解の余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {J C : Type*} [Category* J] [Category* C] [Abelian C]

/--
概要：関手圏の短複体は全ての評価で完全なら完全。
方針：コホモロジーの零性を各成分で証明する。
規約：各評価は有限極限と余極限を保つ。
使われ方：Stacks Theorem 19.12.6、TT §3 の極限順序数での完全性。
-/
lemma shortComplex_exact_of_evaluation (S : ShortComplex (J ⥤ C))
    (h : ∀ j : J, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (Functor.isZero_iff S.homology).mpr
  intro j
  exact ((ShortComplex.exact_iff_isZero_homology _).mp (h j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

end SerrePositivity.KST.DerivedGeometry
