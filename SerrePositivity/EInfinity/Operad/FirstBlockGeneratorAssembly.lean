module

public import SerrePositivity.EInfinity.Operad.FirstBlockSubstitution
public import SerrePositivity.EInfinity.Operad.TensorFamilyGeneratorMap

/-!
# 先頭ブロックへの代入と入力生成射

概要：Berger–Moerdijk §1 の二段の全合成で、内側の演算に生成射を適用して外側へ渡す。
方針：先頭の再結合と生成射の自然性を arity の表示の移送へ持ち上げる。
規約：元の前半の総 arity をまとめた入力族の先頭に置く。
使われ方：Schur 演算の内側のテンソル射を内側の演算の生成射へ変える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：表示を移送した先頭の再結合は入力ごとの生成射と両立する（Berger–Moerdijk §1）。
方針：arity の表示の等式を消去し、先頭の組み込みと有限族の生成射の両立を使う。
規約：X と arity ごとの生成射 e は任意。
使われ方：まとめた先頭の演算の生成射を外側の入力へ渡す。 -/
lemma arityHeadAssembly_generator (X : Complex A) (D : ℕ → Complex A) (e : ∀ r, D r ⟶ X)
    (m : ℕ) (s : Fin (1 + m) → ℕ) (q : ℕ) (t : Fin m → ℕ)
    (hq : q = s ((0 : Fin 1).castAdd m)) (ht : t = fun j => s (j.natAdd 1)) :
    arityHeadAssembly D m s q t hq ht ≫ tensorFamilyGenerator X D e (1 + m) s =
      (e q ⊗ₘ tensorFamilyGenerator X D e m t) ≫ tensorFamilyHeadAssemblyToPower X m := by
  subst q
  subst t
  simpa only [arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    tensorFamilyGenerator_headAssembly X D e m s

/-- 概要：先頭ブロックの再結合はまとめた先頭と後半への生成射の適用に等しい（Berger–Moerdijk §1）。
方針：arity の表示を移送した先頭の再結合の計算則を具体的なブロックの族へ適用する。
規約：先頭の arity は前半の和。
使われ方：内側の全合成の結果に生成射を適用する。 -/
lemma firstBlockFamilyAssembly_generator (X : Complex A) (D : ℕ → Complex A)
    (e : ∀ r, D r ⟶ X) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    firstBlockFamilyAssembly D n m s ≫
      tensorFamilyGenerator X D e (1 + m) (firstBlockArities n m s) =
    (e (∑ j : Fin n, s (j.castAdd m)) ⊗ₘ
      tensorFamilyGenerator X D e m (fun j => s (j.natAdd n))) ≫
      tensorFamilyHeadAssemblyToPower X m := by
  exact arityHeadAssembly_generator X D e m (firstBlockArities n m s)
    (∑ j : Fin n, s (j.castAdd m)) (fun j => s (j.natAdd n))
    (firstBlockArities_head n m s).symm
    (funext fun j => (firstBlockArities_tail n m s j).symm)

/-- 概要：先頭の代入後の生成射は、前半の合成結果への生成射と後半の入力生成射で計算できる（Berger–Moerdijk §1）。
方針：先頭の再結合を生成射へ通し、前半の合成射 f を先頭の生成射へ合成する。
規約：係数 C と前半の入力族を f に渡す。
使われ方：内側の演算のテンソル射を Schur 演算の生成射に置き換える。 -/
lemma firstBlockFamilySubstitution_generator (C X : Complex A) (D : ℕ → Complex A)
    (e : ∀ r, D r ⟶ X) (n m : ℕ) (s : Fin (n + m) → ℕ)
    (f : C ⊗ tensorFamily n (fun j => D (s (j.castAdd m))) ⟶ D (∑ j : Fin n, s (j.castAdd m))) :
    firstBlockFamilySubstitution C D n m s f ≫
      tensorFamilyGenerator X D e (1 + m) (firstBlockArities n m s) =
    (C ◁ (tensorFamilySplitAt n m (fun j => D (s j))).hom) ≫
      (α_ C (tensorFamily n (fun j => D (s (j.castAdd m))))
        (tensorFamily m (fun j => D (s (j.natAdd n))))).inv ≫
      ((f ≫ e (∑ j : Fin n, s (j.castAdd m))) ⊗ₘ
        tensorFamilyGenerator X D e m (fun j => s (j.natAdd n))) ≫
      tensorFamilyHeadAssemblyToPower X m := by
  unfold firstBlockFamilySubstitution
  simp only [Category.assoc]
  rw [firstBlockFamilyAssembly_generator, whiskerRight_comp_tensorHom_assoc]

end SerrePositivity.EInfinity
