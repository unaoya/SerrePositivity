module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullback

/-!
概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackArrow {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    laxPullback p q ⟶ (ihom (Δ[1] : SSet.{u})).obj C := pullback.fst _ _
/-- 概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackFst {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) : laxPullback p q ⟶ A :=
  pullback.snd _ _ ≫ fst A B
/-- 概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackSnd {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) : laxPullback p q ⟶ B :=
  pullback.snd _ _ ≫ snd A B
/-- 概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackArrow_source {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    laxPullbackArrow p q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) =
      laxPullbackFst p q ≫ p := by
  have h := congrArg (fun m ↦ m ≫ fst C C)
    (pullback.condition (f := arrowEndpointPair C) (g := p ⊗ₘ q))
  simpa only [Category.assoc, arrowEndpointPair, lift_fst, tensorHom_fst,
    laxPullbackArrow, laxPullbackFst] using h
/-- 概要：lax pullback の二射影と指定矢印の族の端点。
方針：引き戻しの可換式を二つの射影で評価する。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackArrow_target {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    laxPullbackArrow p q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) =
      laxPullbackSnd p q ≫ q := by
  have h := congrArg (fun m ↦ m ≫ snd C C)
    (pullback.condition (f := arrowEndpointPair C) (g := p ⊗ₘ q))
  simpa only [Category.assoc, arrowEndpointPair, lift_snd, tensorHom_snd,
    laxPullbackArrow, laxPullbackSnd] using h

/-- 概要：lax pullback を定義式の二対象側を先にした引き戻しで表示する。
方針：引き戻しの対称同型を使う。
規約：両端評価と p × q は元の指定射のまま。
使われ方：Tamme Definition 5 の式との厳密な比較。 -/
def laxPullbackFormulaIso {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    laxPullback p q ≅ pullback (p ⊗ₘ q) (arrowEndpointPair C) :=
  pullbackSymmetry _ _
/-- 概要：定義式との同型は元の矢印の族を保つ。
方針：対称同型の第二射影の公式を適用する。
規約：元の指定射との厳密な等式。
使われ方：lax pullback の定義式と矢印のデータの照合。 -/
lemma laxPullbackFormulaIso_arrow {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackFormulaIso p q).hom ≫ pullback.snd (p ⊗ₘ q) (arrowEndpointPair C) =
      laxPullbackArrow p q := pullbackSymmetry_hom_comp_snd _ _
/-- 概要：定義式との同型は二対象の入力を保つ。
方針：対称同型の第一射影の公式を適用する。
規約：元の指定射との厳密な等式。
使われ方：lax pullback の定義式と二射影の照合。 -/
lemma laxPullbackFormulaIso_inputs {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C) :
    (laxPullbackFormulaIso p q).hom ≫ pullback.fst (p ⊗ₘ q) (arrowEndpointPair C) =
      pullback.snd (arrowEndpointPair C) (p ⊗ₘ q) := pullbackSymmetry_hom_comp_fst _ _

end SerrePositivity.InfinityCategories.F2
