module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLift
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurActionGenerators

/-!
模型。文献の定義との比較は後で
# Schur 代数の自由性

概要：Berger–Moerdijk §1 の自由オペラッド代数からの射を、生成元の複体射と対応させる。
方針：各 arity の生成射を生成元への作用で表し、代数射の作用保存から一意性を証明する。
規約：生成元の射は任意の chain map。
使われ方：自由代数関手と忘却関手の随伴の Hom 対応を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

namespace Algebra

/-- 概要：Schur 代数からの代数射の各 arity の値は生成元上の値で計算できる（Berger–Moerdijk §1）。
方針：生成射を生成元への作用で表し、代数射の作用保存則を用いる。
規約：生成元上の値は schurUnit の前合成で与える。
使われ方：自由代数からの代数射の一意性を証明する。 -/
@[reassoc]
lemma freeAlgebraHom_ι {K : Complex A} {X : P.Algebra} (f : P.freeAlgebra K ⟶ X) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n ≫ f.hom =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (P.schurUnit K ≫ f.hom) n) ≫ X.action n := by
  have hf := f.comm n
  change P.schurAction K n ≫ f.hom =
    (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f.hom n) ≫ X.action n at hf
  rw [← P.schurAction_generators K n, Category.assoc, hf, id_tensorHom,
    ← whiskerLeft_comp_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp]

/-- 概要：自由代数からの代数射は生成元上の値で一意に決まる（Berger–Moerdijk §1）。
方針：底の射を Schur の生成射で比較し、各 arity の値の式を使う。
規約：標的は任意の P 代数。
使われ方：生成元の持ち上げの一意性と自由・忘却随伴の逆律を与える。 -/
lemma freeAlgebraHom_ext {K : Complex A} {X : P.Algebra} {f g : P.freeAlgebra K ⟶ X}
    (h : P.schurUnit K ≫ f.hom = P.schurUnit K ≫ g.hom) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schur_hom_ext A P.sequence K X.carrier
  intro n
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.freeAlgebraHom_ι f n, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.freeAlgebraHom_ι g n, h]

/-- 概要：自由代数からの代数射の生成元上の値を持ち上げ直すと元の射になる（Berger–Moerdijk §1）。
方針：生成元による一意性と持ち上げの生成元上の値を用いる。
規約：全 arity の作用を保つ代数射について述べる。
使われ方：自由・忘却随伴の Hom 対応の残りの逆律を与える。 -/
lemma liftHom_restrict {K : Complex A} {X : P.Algebra} (f : P.freeAlgebra K ⟶ X) :
    X.liftHom (P.schurUnit K ≫ f.hom) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.freeAlgebraHom_ext
  exact X.schurUnit_liftHom (P.schurUnit K ≫ f.hom)

end Algebra

/-- 概要：自由代数からの代数射と生成元からの複体射の同値（Berger–Moerdijk §1）。
方針：生成元への制限と既存の代数射の持ち上げを互いに逆な写像として用いる。
規約：底の複体の射は任意の chain map。
使われ方：自由代数関手と忘却関手の随伴を構成する。 -/
def freeAlgebraHomEquiv (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (X : P.Algebra) :
    (P.freeAlgebra K ⟶ X) ≃ (K ⟶ X.carrier) where
  toFun f := P.schurUnit K ≫ f.hom
  invFun f := X.liftHom f
  left_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.liftHom_restrict
  right_inv := X.schurUnit_liftHom

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
