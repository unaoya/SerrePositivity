module

public import SerrePositivity.InfinityCategories.F2.Presentable.PiHomotopyCategory
public import SerrePositivity.InfinityCategories.Core.FunctorComposition

/-!
概要：小さい全直積に値を取る全関手圏を全成分の関手圏の積として表示する。
方針：各指定射影による後合成と、高次自然変換の成分ごとの貼り合わせを使う。
規約：パラメーター圏の小ささを要求しない。
使われ方：小さい族の反映の全随伴の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全成分の高次自然変換を元の直積値の高次自然変換へ貼り合わせる。
方針：元の各単体で全成分を並べる。
規約：同じパラメーター T を保持する。
使われ方：関手圏の直積比較の逆写像。 -/
def functorPiGlue {ι : Type u} (T : SSet.{u + 1}) (C : ι → SSet.{u + 1}) :
    piSSet (fun i ↦ (ihom T).obj (C i)) ⟶ (ihom T).obj (piSSet C) where
  app _ := ↾fun f ↦ {
    app d α := ↾fun x i ↦ (f i).app d α x
    naturality {d e} β α := by
      apply ConcreteCategory.hom_ext
      intro x
      funext i
      exact congrArg (fun q : T.obj d ⟶ (C i).obj e ↦ q x) ((f i).naturality β α) }
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    rfl

/-- 概要：直積値の全関手圏は元の成分の全関手圏の直積と同型。
方針：元の各射影による後合成と全成分の貼り合わせを逆にする。
規約：指定射影自体を順方向の成分とする。
使われ方：直積の全パラメーターの Hom 対応。 -/
def functorPiIso {ι : Type u} (T : SSet.{u + 1}) (C : ι → SSet.{u + 1}) :
    (ihom T).obj (piSSet C) ≅ piSSet (fun i ↦ (ihom T).obj (C i)) where
  hom := piSSetLift (fun i ↦ (ihom T).map (piSSetProjection C i))
  inv := functorPiGlue T C
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    funext i
    apply CategoryTheory.Functor.functorHom_ext
    intro d α
    apply ConcreteCategory.hom_ext
    intro x
    rfl

end SerrePositivity.InfinityCategories.F2.Presentable
