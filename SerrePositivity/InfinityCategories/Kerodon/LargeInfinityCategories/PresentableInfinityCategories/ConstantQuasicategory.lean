module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.DiscreteComponentLabels
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-!
概要：小さい型の定値単体集合の quasicategory 性を離散 nerve から回収する。
方針：零番目の対象で評価し、元の定値図式を離散 nerve の retract にする。
規約：モデル構造の instance は使わない。
使われ方：小さい底の直和の射影の底を構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：離散 nerve の元の単体をその零番目のラベルへ戻す。
方針：離散圏の全ての矢印が対象の等式を与えることを使う。
規約：次数ごとに同じ元の型 T へ写す。
使われ方：定値単体集合の retract の射影。 -/
def discreteNerveToConstant (T : Type u) :
    nerve (Discrete T) ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj T where
  app _ := ↾fun s ↦ (s.obj 0).as
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro s
    change (s.obj (α.unop.toOrderHom 0)).as = (s.obj 0).as
    exact (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le _)))).symm

/-- 概要：元の定値図式のラベルを離散 nerve から戻すと恒等。
方針：元の定値関手の零番目の対象を評価する。
規約：全単体集合の射の等式。
使われ方：ホーンの充填の移送。 -/
lemma constantToDiscreteNerve_retraction (T : Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.constantToDiscreteNerve T ≫ discreteNerveToConstant T = 𝟙 _ := rfl

/-- 概要：小さい型の定値単体集合は quasicategory。
方針：離散 nerve 内で埋めたホーンを元の定値図式へ戻す。
規約：元の定値単体集合の同じホーンを充填する。
使われ方：小さい quasicategory の直和を作る射影の底。 -/
lemma constant_isQuasicategory (T : Type u) :
    Quasicategory ((CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj T) := by
  constructor
  intro n i f hi hn
  obtain ⟨s, hs⟩ := Quasicategory.hornFilling hi hn (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.constantToDiscreteNerve T)
  refine ⟨s ≫ discreteNerveToConstant T, ?_⟩
  have h := congrArg (fun q ↦ q ≫ discreteNerveToConstant T) hs
  simpa only [Category.assoc, constantToDiscreteNerve_retraction, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
