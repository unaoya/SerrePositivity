module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OppositeMap
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.OppositeSimplexEquiv

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
open _root_.CategoryTheory _root_.Opposite
namespace SerrePositivity.InfinityCategories.HTT.Section6_1_2

variable (C : Type u) [Category.{u} C]

/-- 概要：反対圏の nerve と元の nerve の順序反転の実単体的同型。
方針：各次数の実全単射を、証明済みの実単体写像の自然性で束ねる。
規約：幾何学的実現を用いず元の単体集合の同型を構成する。
使われ方：Over と Under の nerve の比較。 -/
def nerveOppositeIso : nerve Cᵒᵖ ≅ (nerve C).op :=
  NatIso.ofComponents
    (fun k ↦ Equiv.toIso ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplexEquiv C k.unop.len).trans
      (SSet.opObjEquiv (X := nerve C) (n := k)).symm))
    (fun φ ↦ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveOppositeMap C).naturality φ)

/-- 概要：反対 nerve の実同型は圏の実関手に自然。
方針：反転した列を関手で送る二つの順序を定義で評価する。
規約：通常の指定された関手についての自然性。
使われ方：反転した射影と図式の照合。 -/
lemma nerveOppositeIso_natural {D : Type u} [Category.{u} D] (f : C ⥤ D) :
    nerveMap f.op ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso D).hom =
      (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso C).hom ≫ SSet.opFunctor.map (nerveMap f) := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 概要：反対圏の nerve の反転を元の圏の nerve へ戻す。
方針：反対 nerve の同型を反転し二重反転を消去する。
規約：単体集合の指定された同型を使う。
使われ方：左 Kan の slice の古典表示。 -/
def nerveUnopIso : (nerve Cᵒᵖ).op ≅ nerve C :=
  SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso C) ≪≫
    SSet.opFunctorCompOpFunctorIso.app (nerve C)

/-- 概要：反対 nerve を戻す同型は通常の関手に自然。
方針：反転した射列への関手の作用を両辺で計算する。
規約：反対関手を nerve に写した後に単体を反転する。
使われ方：Over と Under の忘却射影の照合。 -/
lemma nerveUnopIso_natural {D : Type u} [Category.{u} D] (F : C ⥤ D) :
    SSet.opFunctor.map (nerveMap F.op) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso D).hom =
      (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom ≫ nerveMap F := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.HTT.Section6_1_2

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "6.1.2.2" (partial := special) "仮定：C を通常圏 D の nerve に特殊化（Lean が強い）。結論：Δop→D と Δ+op→D としての単体対象・増大単体対象の定義は一致。増大対象の Mathlib 表示との同値、反対圏と関手圏の nerve の同型もある。任意の準圏 C 全体の定義ではない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso
attribute [cite HTT "6.1.2.3"] _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso
attribute [cite HTT "6.5.3.1" (partial := special) "仮定：presentable X を通常圏 D の nerve に特殊化し、対応する ordinary right Kan extensions が存在（Lean が強い。D と Hom は nerve 比較と同じ宇宙に配置）。結論：Δ≤n への制限、その right Kan extension の右随伴、両者の合成としての coskeleton は一致。関手圏・反対圏の nerve 同型と随伴の nerve 比較を併用する。任意の準圏 X の coskeleton 全体は含まない。"] _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso
