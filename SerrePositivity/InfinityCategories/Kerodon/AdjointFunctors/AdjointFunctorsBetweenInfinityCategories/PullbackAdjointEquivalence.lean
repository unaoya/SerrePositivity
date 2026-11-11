module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
概要：通常の引き戻し関手の右随伴の存在は圏同値で移送できる。
方針：slice の同値で map と pullback の随伴を共役し、右随伴の一意性を使う。
規約：元の圏の対象・Hom の宇宙は両辺で異なってよい。
使われ方：小さい Hom を持つ単体添字圏を持ち上げて前層圏の一般補題を適用する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：slice への圏同値の作用は底の射の後合成と可換。
方針：各成分で恒等射を使い、底への可換性は関手の合成保存。
規約：ここでは任意の関手 F に成立する。
使われ方：引き戻し随伴を圏同値で共役する。 -/
def cofinalOverMapPostIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {E B : C} (p : E ⟶ B) :
    Over.map p ⋙ Over.post F ≅ Over.post F ⋙ Over.map (F.map p) :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Iso.refl _) (by simp))
    (by intro X Y f; apply Over.OverMorphism.ext; simp)

/-- 概要：圏同値の先で引き戻しが左随伴なら、元の引き戻しも左随伴。
方針：map と pullback の随伴を slice の同値で共役し、右随伴の一意性で同定する。
規約：右随伴の存在は同値先の引き戻しについてだけ仮定する。
使われ方：前層の添字圏の宇宙の持ち上げ後に単体集合へ戻す。 -/
lemma cofinalPullback_isLeftAdjoint_of_equivalence {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] [HasPullbacks C] [HasPullbacks D]
    (e : C ≌ D) {E B : C} (p : E ⟶ B)
    [(Over.pullback (e.functor.map p)).IsLeftAdjoint] : (Over.pullback p).IsLeftAdjoint := by
  let eE := Over.postEquiv (X := E) e
  let eB := Over.postEquiv (X := B) e
  let adj := eE.toAdjunction.comp ((Over.mapPullbackAdj (e.functor.map p)).comp
    eB.symm.toAdjunction)
  let isoL : eE.functor ⋙ (Over.map (e.functor.map p) ⋙ eB.inverse) ≅ Over.map p :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (cofinalOverMapPostIso e.functor p).symm eB.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.map p) eB.unitIso.symm ≪≫ Functor.rightUnitor _
  let adj' := adj.ofNatIsoLeft isoL
  let isoR := (Over.mapPullbackAdj p).rightAdjointUniq adj'
  have : ((eB.functor ⋙ Over.pullback (e.functor.map p)) ⋙ eE.inverse).IsLeftAdjoint :=
    inferInstance
  exact Functor.isLeftAdjoint_of_iso isoR.symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
