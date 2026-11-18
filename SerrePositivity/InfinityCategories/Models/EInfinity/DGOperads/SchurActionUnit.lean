module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurGeneratorExt

/-!
模型。文献の定義との比較は後で
# Schur 対象上の作用射の単位則

概要：Berger–Moerdijk §1 の単位演算が、構成した Schur 作用で恒等射として作用することを証明する。
方針：一次の入力の生成射上で作用を計算し、生成射による一意性を用いる。
規約：テンソル冪の一次比較同型は既存の `oneIso` を使う。
使われ方：Schur 対象を自由オペラッド代数として束ねる際の単位作用の証明となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：一次の Schur 入力の生成射は一次テンソル冪の比較同型と両立する（Berger–Moerdijk §1）。
方針：生成射の右単位子の自然性を使う。
規約：内側 arity の有限族は一要素。
使われ方：Schur 作用の単位則の右辺を生成射上で計算する。 -/
@[reassoc]
lemma schurInputGenerator_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (s : Fin 1 → ℕ) :
    P.schurInputGenerator K 1 s ≫ (oneIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)).hom =
      (ρ_ (P.arity (s 0) ⊗ power K (s 0))).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s 0) := by
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (s 0) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫
    (ρ_ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)).hom = _
  rw [tensorHom_id]
  exact rightUnitor_naturality _

/-- 概要：Schur 対象上の作用射は単位演算を恒等射として作用させる（Berger–Moerdijk §1）。
方針：一次の入力の生成射で制限し、生成射上の単位作用と単位子の自然性を使う。
規約：代数の単位作用の公理と同じ型で述べる。
使われ方：自由オペラッド代数の `unit_action` の証明となる。 -/
lemma schurAction_unit (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) :
    (P.unit ▷ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) 1) ≫ P.schurAction K 1 =
      (λ_ (power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K) 1)).hom ≫
        (oneIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)).hom := by
  apply P.schurInputGenerator_hom_ext K 1 (𝟙_ (Complex A)) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K)
  intro s
  rw [whisker_exchange_assoc, P.schurInputGenerator_action,
    P.schurOperationGenerator_unit, leftUnitor_naturality_assoc, P.schurInputGenerator_one]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
