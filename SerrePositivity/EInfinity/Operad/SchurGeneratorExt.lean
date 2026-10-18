module

public import SerrePositivity.EInfinity.Operad.SchurComposition
public import SerrePositivity.EInfinity.Operad.SchurTensorExt
public import SerrePositivity.EInfinity.Operad.TensorGeneratorExt

/-!
# 任意個の Schur 入力の生成射による一意性

概要：Berger–Moerdijk §1 の自由代数の演算の一意性を、入力ごとの arity で判定する。
方針：Schur 図式の余極限保存を一因子ずつ適用する。
規約：arity 0 と空の入力族を含める。
使われ方：自由代数の作用の公理と随伴の射の一意性を生成射上で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

namespace Operad

variable {A : Type u} [CommRing A]

/-- 概要：Schur 入力の任意の有限テンソル冪からの射は生成射上で決まる（Berger–Moerdijk §1）。
方針：入力数の帰納法で先頭の Schur 因子を生成射に制限し、残りに帰納法を使う。
規約：左の固定因子も任意であり、自由代数の作用を仮定しない。
使われ方：Schur 対象上の自由代数の作用と代数射の一意性に用いる。 -/
lemma schurInputGenerator_hom_ext (P : Operad A) (K : Complex A) (n : ℕ)
    (C Y : Complex A) (f g : C ⊗ power ((schurFunctor A P.sequence).obj K) n ⟶ Y)
    (h : ∀ s : Fin n → ℕ, (C ◁ P.schurInputGenerator K n s) ≫ f =
      (C ◁ P.schurInputGenerator K n s) ≫ g) : f = g := by
  exact tensorFamilyGenerator_hom_ext ((schurFunctor A P.sequence).obj K)
    (fun i => P.arity i ⊗ power K i) (fun i => schurι A P.sequence K i)
    (fun C T Y f g h => schur_tensorMiddle_hom_ext P.sequence K C T Y f g h) n C Y f g h

end Operad

end SerrePositivity.EInfinity
