module

public import SerrePositivity.InfinityCategories.F1B.KanNerveOppositeMap
public import SerrePositivity.InfinityCategories.F1B.KanNerveOppositeSimplexEquiv

/-!
概要：反対圏の nerve と単体の反転を自然な同型で同定する。
方針：射列の順序と矢印を反転し二重反転を消去する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の局所添字の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
namespace SerrePositivity.InfinityCategories.F1B

variable (C : Type u) [Category.{u} C]

/-- 概要：反対圏の nerve と元の nerve の順序反転の実単体的同型。
方針：各次数の実全単射を、証明済みの実単体写像の自然性で束ねる。
規約：幾何学的実現を用いず元の単体集合の同型を構成する。
使われ方：Over と Under の nerve の比較。 -/
def kanNerveOppositeIso : nerve Cᵒᵖ ≅ (nerve C).op :=
  NatIso.ofComponents
    (fun k ↦ Equiv.toIso ((kanOppositeNerveSimplexEquiv C k.unop.len).trans
      (SSet.opObjEquiv (X := nerve C) (n := k)).symm))
    (fun φ ↦ (kanNerveOppositeMap C).naturality φ)

/-- 概要：反対 nerve の実同型は圏の実関手に自然。
方針：反転した列を関手で送る二つの順序を定義で評価する。
規約：通常の指定された関手についての自然性。
使われ方：反転した射影と図式の照合。 -/
lemma kanNerveOppositeIso_natural {D : Type u} [Category.{u} D] (f : C ⥤ D) :
    nerveMap f.op ≫ (kanNerveOppositeIso D).hom =
      (kanNerveOppositeIso C).hom ≫ SSet.opFunctor.map (nerveMap f) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：反対圏の nerve の反転を元の圏の nerve へ戻す。
方針：反対 nerve の同型を反転し二重反転を消去する。
規約：単体集合の指定された同型を使う。
使われ方：左 Kan の slice の古典表示。 -/
def kanNerveUnopIso : (nerve Cᵒᵖ).op ≅ nerve C :=
  SSet.opFunctor.mapIso (kanNerveOppositeIso C) ≪≫
    SSet.opFunctorCompOpFunctorIso.app (nerve C)

/-- 概要：反対 nerve を戻す同型は通常の関手に自然。
方針：反転した射列への関手の作用を両辺で計算する。
規約：反対関手を nerve に写した後に単体を反転する。
使われ方：Over と Under の忘却射影の照合。 -/
lemma kanNerveUnopIso_natural {D : Type u} [Category.{u} D] (F : C ⥤ D) :
    SSet.opFunctor.map (nerveMap F.op) ≫ (kanNerveUnopIso D).hom =
      (kanNerveUnopIso C).hom ≫ nerveMap F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.F1B
