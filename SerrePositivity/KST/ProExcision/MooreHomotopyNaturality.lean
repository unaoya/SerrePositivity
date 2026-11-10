module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy

/-!
# Moore 収縮ホモトピーの成分の自然性

概要：Mathlib の Moore 射影と恒等の実鎖ホモトピーが入力の射に自然であることを証明する。
方針：退化による基本ホモトピーから有限段階の帰納法を通し、PInfty の各成分へ移す。
規約：KST Construction A.5、正規化比較の外部群同変性のための補題。
使われ方：Moore 収縮のテンソルの自然性へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {X Y : SimplicialObject A} (f : X ⟶ Y)

/-- 概要：Moore 収縮の基本退化ホモトピーの一段上の成分は自然。
方針：nullHomotopy の成分を退化写像の自然性へ帰着する。
規約：KST A.5。使われ方：有限段階の Moore 収縮の帰納法。 -/
lemma mooreHsigmaHomotopy_naturality (q n : ℕ) :
    f.app (op ⦋n⦌) ≫ (homotopyHσToZero (X := Y) q).hom n (n + 1) =
      (homotopyHσToZero (X := X) q).hom n (n + 1) ≫ f.app (op ⦋n + 1⦌) := by
  simp only [homotopyHσToZero, Homotopy.nullHomotopy'_hom,
    show (ComplexShape.down ℕ).Rel (n + 1) n from rfl, dite_true]
  exact hσ'_naturality q n (n + 1) rfl f

/-- 概要：有限段階の Moore 射影と恒等のホモトピーの一段上の成分は自然。
方針：退化ホモトピーと射影の自然性を段階 q に関して帰納的に合成する。
規約：KST A.5。使われ方：PInfty 収縮の各成分の自然性。 -/
lemma mooreFiniteHomotopy_naturality (q n : ℕ) :
    f.app (op ⦋n⦌) ≫ (homotopyPToId Y q).hom n (n + 1) =
      (homotopyPToId X q).hom n (n + 1) ≫ f.app (op ⦋n + 1⦌) := by
  induction q with
  | zero =>
    simp only [homotopyPToId, Homotopy.refl_hom, Limits.comp_zero, Limits.zero_comp]
  | succ q ih =>
    simp only [homotopyPToId, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Homotopy.add_hom, Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero,
      Preadditive.comp_add, Preadditive.add_comp]
    rw [ih, ← Category.assoc, P_f_naturality, Category.assoc,
      mooreHsigmaHomotopy_naturality f, ← Category.assoc]

/-- 概要：Moore の PInfty 収縮の一段上の成分は全ての入力射に自然。
方針：各成分を有限段階のホモトピーへ同定する。
規約：KST Construction A.5、任意の前加法圏。
使われ方：正規化 EZ 比較の外部作用の同変性。 -/
lemma moorePInftyHomotopy_naturality (n : ℕ) :
    f.app (op ⦋n⦌) ≫ (homotopyPInftyToId Y).hom n (n + 1) =
      (homotopyPInftyToId X).hom n (n + 1) ≫ f.app (op ⦋n + 1⦌) :=
  mooreFiniteHomotopy_naturality f (n + 1 + 1) n

end SerrePositivity.KST.ProExcision
