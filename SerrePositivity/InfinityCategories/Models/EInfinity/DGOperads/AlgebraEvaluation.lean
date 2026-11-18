module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperations

/-!
模型。文献の定義との比較は後で
# オペラッド代数の Schur 評価射

概要：Berger–Moerdijk §1 の自由代数の Hom 対応に使う生成元包含と評価射を構成する。
方針：各 arity の作用を Schur の普遍性で束ね、単位則と代数射との両立を示す。
規約：自由代数の存在やその作用を仮定しない。
使われ方：自由・忘却随伴の単位と余単位を構成するために用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

namespace Operad

/-- 概要：オペラッドの単位から Schur 対象への生成元包含（Berger–Moerdijk §1）。
方針：一次テンソル冪の同型、単位子、arity 1 の単位演算を合成する。
規約：この段階では自由代数の作用を必要としない。
使われ方：自由・忘却随伴の単位となる。 -/
def schurUnit (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) : K ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K :=
  (oneIso K).inv ≫ (λ_ (power K 1)).inv ≫ (P.unit ▷ power K 1) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K 1

/-- 概要：Schur 生成元包含は底の複体に関して自然（Berger–Moerdijk §1）。
方針：一次テンソル冪の比較、単位子、Schur 生成射の自然性を用いる。
規約：オペラッドの単位演算を固定する。
使われ方：自由・忘却随伴の単位の自然性を得る。 -/
@[reassoc]
lemma schurUnit_naturality (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) {K L : Complex A} (f : K ⟶ L) :
    f ≫ P.schurUnit L = P.schurUnit K ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f := by
  have hone : (oneIso K).inv ≫ _root_.SerrePositivity.TensorPowers.map f 1 = f ≫ (oneIso L).inv := by
    apply (cancel_mono (oneIso L).hom).1
    rw [Category.assoc, oneIso_naturality]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  symm
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality, id_tensorHom]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  rw [← Category.assoc (oneIso K).inv (_root_.SerrePositivity.TensorPowers.map f 1), hone, Category.assoc]

/-- 概要：Schur 生成元包含の自然変換（Berger–Moerdijk §1）。
方針：単位演算からの包含の自然性を束ねる。
規約：自由代数上の作用やモナド則をまだ仮定しない。
使われ方：自由代数の随伴の単位を構成する。 -/
def schurUnitNatTrans (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : 𝟭 (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence where
  app K := P.schurUnit K
  naturality {_K _L} f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit_naturality P f

namespace Algebra

variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：代数の作用を等変な演算族として読む（Berger–Moerdijk §1）。
方針：代数の action と equivariance をそのまま用いる。
規約：合成則と単位則を消去せず、ここでは等変性の部分だけを取り出す。
使われ方：Schur 対象から代数への評価射を作る。 -/
def operationFamily (X : P.Algebra) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationFamily P.sequence X.carrier X.carrier where
  app := X.action
  equivariance := X.equivariance

/-- 概要：Schur 対象から代数の底への評価射（Berger–Moerdijk §1）。
方針：等変な作用族を余極限からの射へ降ろす。
規約：自由代数上の作用の構成を仮定しない。
使われ方：自由・忘却随伴の余単位と Hom 対応に用いる。 -/
def evaluation (X : P.Algebra) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj X.carrier ⟶ X.carrier :=
  X.operationFamily.desc

/-- 概要：評価射は各 arity の作用を再現する（Berger–Moerdijk §1）。
方針：Schur の降下射の生成射上の等式を用いる。
規約：arity 0 の作用も含む。
使われ方：代数射と評価射の両立を生成射で確認する。 -/
@[reassoc]
lemma ι_evaluation (X : P.Algebra) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence X.carrier n ≫ X.evaluation = X.action n :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationFamily.ι_desc X.operationFamily n

/-- 概要：生成元包含の後に代数で評価すると恒等射になる（Berger–Moerdijk §1）。
方針：arity 1 の生成射を評価し、代数の単位作用の公理を用いる。
規約：底の複体射としての等式を示す。
使われ方：自由・忘却随伴の三角恒等式の一方に用いる。 -/
@[reassoc]
lemma schurUnit_evaluation (X : P.Algebra) :
    P.schurUnit X.carrier ≫ X.evaluation = 𝟙 X.carrier := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ι_evaluation]
  rw [X.unit_action]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- 概要：評価射は代数射と両立する（Berger–Moerdijk §1）。
方針：Schur 生成射上で代数射の作用保存則に帰着する。
規約：底の射に Schur 関手を適用する。
使われ方：自由・忘却随伴の余単位の自然性を得る。 -/
@[reassoc]
lemma evaluation_naturality {X Y : P.Algebra} (f : X ⟶ Y) :
    X.evaluation ≫ f.hom = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f.hom ≫ Y.evaluation := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schur_hom_ext A P.sequence X.carrier Y.carrier
  intro n
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ι_evaluation_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ι_evaluation]
  exact f.comm n

/-- 概要：Schur 評価射は忘却関手上の自然変換をなす（Berger–Moerdijk §1）。
方針：代数射との両立を自然性の公理として用いる。
規約：自由代数関手をまだ仮定しない底の複体への自然変換。
使われ方：随伴の余単位の底の射を与える。 -/
def evaluationNatTrans (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P where
  app X := X.evaluation
  naturality {_X _Y} f := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.evaluation_naturality f).symm

/-- 概要：生成元の chain map を Schur 対象からの射へ拡張する（Berger–Moerdijk §1）。
方針：Schur 関手で生成元の射を送り、標的代数の評価射を合成する。
規約：この射が代数射であるという主張には自由代数上の作用の構成が別途必要。
使われ方：自由・忘却随伴の Hom 対応の逆写像の底の射となる。 -/
def schurLift {K : Complex A} (Y : P.Algebra) (f : K ⟶ Y.carrier) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj K ⟶ Y.carrier :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map f ≫ Y.evaluation

/-- 概要：Schur 拡張の各 arity の値（Berger–Moerdijk §1）。
方針：生成射の自然性と標的代数の評価の式を用いる。
規約：生成元の射を全入力へ同時に適用する。
使われ方：拡張の作用保存則を生成元で確認する。 -/
@[reassoc]
lemma ι_schurLift {K : Complex A} (Y : P.Algebra) (f : K ⟶ Y.carrier) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n ≫ Y.schurLift f =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f n) ≫ Y.action n := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι_naturality_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ι_evaluation]

/-- 概要：Schur 拡張は指定した生成元の射を延長する（Berger–Moerdijk §1）。
方針：生成元包含の自然性と代数の単位作用を用いる。
規約：自由代数の存在を仮定せず底の複体の等式として証明する。
使われ方：自由・忘却随伴の Hom 対応の片側の逆律を証明する。 -/
@[reassoc]
lemma schurUnit_schurLift {K : Complex A} (Y : P.Algebra) (f : K ⟶ Y.carrier) :
    P.schurUnit K ≫ Y.schurLift f = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurUnit_naturality_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurUnit_evaluation, Category.comp_id]

/-- 概要：Schur 拡張は生成元の前合成と両立する（Berger–Moerdijk §1）。
方針：Schur 関手の合成保存則を用いる。
規約：標的の代数を固定する。
使われ方：自由・忘却随伴の Hom 対応の源に関する自然性を得る。 -/
@[reassoc]
lemma schurLift_precomp {K L : Complex A} (Y : P.Algebra) (h : K ⟶ L) (f : L ⟶ Y.carrier) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).map h ≫ Y.schurLift f = Y.schurLift (h ≫ f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, Functor.map_comp, Category.assoc]

/-- 概要：Schur 拡張は標的の代数射との後合成と両立する（Berger–Moerdijk §1）。
方針：評価射の自然性と Schur 関手の合成保存則を用いる。
規約：後合成は作用を保存する代数射である。
使われ方：自由・忘却随伴の Hom 対応の標的に関する自然性を得る。 -/
@[reassoc]
lemma schurLift_postcomp {K : Complex A} {Y Z : P.Algebra}
    (f : K ⟶ Y.carrier) (g : Y ⟶ Z) :
    Y.schurLift f ≫ g.hom = Z.schurLift (f ≫ g.hom) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.schurLift, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.evaluation_naturality,
    Functor.map_comp, Category.assoc]

end Algebra

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
