module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：直積値の全関手圏を二つの全関手圏の直積へ元の射影で分解する。
方針：内部 Hom の右随伴としての積保存から指定した標準比較同型を取る。
規約：関手圏と直積は元の単体集合を使い、Hom 集合だけへは制限しない。
使われ方：積の反映模型と全随伴の成分表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：直積値の元の全関手圏は二つの成分関手圏の直積と同型。
方針：内部 Hom の右随伴の積保存を使う。
規約：始域 T の小ささ・充填性を要求しない。
使われ方：presentable な積の反映模型。 -/
def functorTensorIso (T X Y : SSet.{u}) :
    (ihom T).obj (X ⊗ Y) ≅ (ihom T).obj X ⊗ (ihom T).obj Y :=
  asIso (prodComparison (ihom T) X Y)

/-- 概要：全関手圏の積比較の第一成分は元の第一射影による後合成。
方針：標準積比較の第一脚の式を使う。
規約：元の全射の等式。
使われ方：全随伴の成分表示の第一射影。 -/
lemma functorTensorIso_hom_fst (T X Y : SSet.{u}) :
    (functorTensorIso T X Y).hom ≫ fst ((ihom T).obj X) ((ihom T).obj Y) =
      (ihom T).map (fst X Y) := by
  exact prodComparison_fst (ihom T) X Y

/-- 概要：全関手圏の積比較の第二成分は元の第二射影による後合成。
方針：標準積比較の第二脚の式を使う。
規約：元の全射の等式。
使われ方：全随伴の成分表示の第二射影。 -/
lemma functorTensorIso_hom_snd (T X Y : SSet.{u}) :
    (functorTensorIso T X Y).hom ≫ snd ((ihom T).obj X) ((ihom T).obj Y) =
      (ihom T).map (snd X Y) := by
  exact prodComparison_snd (ihom T) X Y

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
