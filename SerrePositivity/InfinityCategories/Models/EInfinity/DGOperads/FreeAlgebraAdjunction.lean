module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraUniversal
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
模型。文献の定義との比較は後で
# 自由オペラッド代数と忘却関手の随伴

概要：Berger–Moerdijk §1 の自由 P 代数関手と底の複体への忘却関手の随伴を構成する。
方針：生成元への制限と代数射の持ち上げの Hom 対応、および両変数の自然性を束ねる。
規約：Schur 関手で構成した自由代数関手をそのまま用いる。
使われ方：E∞ 代数へのモデル構造の転送の自由・忘却随伴となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：自由オペラッド代数関手は忘却関手の左随伴である（Berger–Moerdijk §1）。
方針：生成元への制限と持ち上げの互いに逆な Hom 対応を自然な同値として用いる。
規約：追加の自由性や持ち上げの一意性の仮定を要求しない。
使われ方：オペラッド代数の転送モデル構造の入力となる。 -/
def freeAlgebraAdjunction (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : P.freeAlgebraFunctor ⊣ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P :=
  Adjunction.mkOfHomEquiv {
    homEquiv := P.freeAlgebraHomEquiv
    homEquiv_naturality_left_symm := fun {_K _L X} f g => (X.liftHom_precomp f g).symm
    homEquiv_naturality_right := fun {K _X _Y} f g =>
      (Category.assoc (P.schurUnit K) f.hom g.hom).symm }

/-- 概要：随伴の Hom 対応は構成した生成元への制限と持ち上げの同値である（Berger–Moerdijk §1）。
方針：随伴の構成の Hom 同値の成分を評価する。
規約：対象 K と代数 X を固定した同値の等式。
使われ方：随伴による射の対応を具体的に計算する。 -/
lemma freeAlgebraAdjunction_homEquiv (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (X : P.Algebra) :
    P.freeAlgebraAdjunction.homEquiv K X = P.freeAlgebraHomEquiv K X := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.freeAlgebraAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- 概要：自由・忘却随伴の単位は生成元の包含である（Berger–Moerdijk §1）。
方針：恒等代数射を生成元へ制限する。
規約：底の複体 K での単位の成分。
使われ方：自由代数を生成元によって扱う際の随伴の単位を同定する。 -/
lemma freeAlgebraAdjunction_unit_app (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) :
    P.freeAlgebraAdjunction.unit.app K = P.schurUnit K := by
  change P.schurUnit K ≫ 𝟙 _ = P.schurUnit K
  exact Category.comp_id _

/-- 概要：自由・忘却随伴の余単位は評価代数射である（Berger–Moerdijk §1）。
方針：恒等複体射の持ち上げを計算する。
規約：任意の P 代数 X での余単位の成分。
使われ方：転送と忘却の比較で余単位を評価射として用いる。 -/
lemma freeAlgebraAdjunction_counit_app (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (X : P.Algebra) :
    P.freeAlgebraAdjunction.counit.app X = X.evaluationHom := by
  change X.liftHom (𝟙 X.carrier) = X.evaluationHom
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.liftHom]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
