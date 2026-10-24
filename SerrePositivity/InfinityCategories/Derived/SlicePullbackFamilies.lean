module
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTransport
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceProjectionLaws
/-!
概要：引き戻し圏内の実 slice の全錐を、両成分の厳密に整合する全錐として表示する。
方針：slice の普遍性と元の引き戻しの普遍性を二度適用する。
規約：固定図式と全パラメータを保持。使われ方：右 Kan の slice の分子と商側三角形の分離。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
variable {K E F B A : SSet.{u}} (f : E ⟶ B) (g : F ⟶ B) (a : K ⟶ pullback f g)
/-- 元の引き戻しの二つの固定図式は同じ底を持つ。 -/
lemma slicePullbackPoint_comm : (a ≫ pullback.fst f g) ≫ f =
    (a ≫ pullback.snd f g) ≫ g := by
  rw [Category.assoc, pullback.condition, Category.assoc]
/-- 右成分の slice を、左成分と同じ厳密な底図式へ送る。 -/
def slicePullbackRightMap : sliceOver (a ≫ pullback.snd f g) ⟶
    sliceOver ((a ≫ pullback.fst f g) ≫ f) :=
  sliceOverPostcomp _ g ≫
    (eqToIso (congrArg sliceOver (slicePullbackPoint_comm f g a).symm)).hom
/-- 同じ厳密な底へ輸送した右成分の始域射影。 -/
lemma slicePullbackRightMap_projection :
    slicePullbackRightMap f g a ≫ sliceOverProjection ((a ≫ pullback.fst f g) ≫ f) =
      sliceOverProjection (a ≫ pullback.snd f g) ≫ g := by
  dsimp only [slicePullbackRightMap]
  rw [Category.assoc,
    SerrePositivity.InfinityCategories.F1B.sliceOverProjection_eqTransport (slicePullbackPoint_comm f g a).symm,
    SerrePositivity.InfinityCategories.F1B.sliceOverPostcomp_projection]
/-- 等式による図式の輸送は、全パラメータの錐の展開を変えない。 -/
lemma sliceTransport_uncurry {Y : SSet.{u}} {p q : K ⟶ Y} (h : p = q)
    (s : A ⟶ sliceOver p) :
    sliceOverUncurry (s ≫ (eqToIso (congrArg sliceOver h)).hom) = sliceOverUncurry s := by
  cases h
  rw [eqToIso_refl, Iso.refl_hom, Category.comp_id]
/-- 同じ底へ輸送した右成分の全錐の展開。 -/
lemma slicePullbackRightMap_uncurry (s : A ⟶ sliceOver (a ≫ pullback.snd f g)) :
    sliceOverUncurry (s ≫ slicePullbackRightMap f g a) = sliceOverUncurry s ≫ g := by
  dsimp only [slicePullbackRightMap]
  rw [← Category.assoc,
    sliceTransport_uncurry (slicePullbackPoint_comm f g a).symm, sliceOverUncurry_postcomp]
/-- 引き戻し内の全錐を二成分へ写すと、底の全錐は厳密に一致する。 -/
lemma slicePullbackPostcomp_comm :
    sliceOverPostcomp a (pullback.fst f g) ≫ sliceOverPostcomp (a ≫ pullback.fst f g) f =
      sliceOverPostcomp a (pullback.snd f g) ≫ slicePullbackRightMap f g a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro c
  apply Subtype.ext
  change (c.val ≫ pullback.fst f g) ≫ f = _
  change (c.val ≫ pullback.fst f g) ≫ f =
    ((eqToIso (congrArg sliceOver (slicePullbackPoint_comm f g a).symm)).hom.app n
      ((sliceOverPostcomp (a ≫ pullback.snd f g) g).app n
        ((sliceOverPostcomp a (pullback.snd f g)).app n c))).val
  rw [roofSliceTransport_val (slicePullbackPoint_comm f g a).symm]
  change (c.val ≫ pullback.fst f g) ≫ f = (c.val ≫ pullback.snd f g) ≫ g
  rw [Category.assoc, pullback.condition, Category.assoc]
/-- 同じ底を持つ二成分の slice の全空間。 -/
def slicePullbackDiagram : SSet.{u} :=
  pullback (sliceOverPostcomp (a ≫ pullback.fst f g) f) (slicePullbackRightMap f g a)
/-- 元の引き戻し内の全錐を、両成分の整合する全錐へ写す。 -/
def slicePullbackMap : sliceOver a ⟶ slicePullbackDiagram f g a :=
  pullback.lift (sliceOverPostcomp a (pullback.fst f g))
    (sliceOverPostcomp a (pullback.snd f g)) (slicePullbackPostcomp_comm f g a)
/-- 二成分の整合する全錐を展開すると、元の底で同じ実 join 図式を持つ。 -/
lemma slicePullbackFamily_comm (s : A ⟶ slicePullbackDiagram f g a) :
    sliceOverUncurry (s ≫ pullback.fst _ _) ≫ f =
      sliceOverUncurry (s ≫ pullback.snd _ _) ≫ g := by
  rw [← sliceOverUncurry_postcomp, ← slicePullbackRightMap_uncurry]
  apply congrArg sliceOverUncurry
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => s ≫ k) (pullback.condition (f :=
      sliceOverPostcomp (a ≫ pullback.fst f g) f) (g := slicePullbackRightMap f g a))).trans
        (Category.assoc _ _ _).symm)
/-- 整合する二成分の全錐を、元の引き戻し内の一つの全錐へ戻す。 -/
def slicePullbackBackwardFamily (s : A ⟶ slicePullbackDiagram f g a) : A ⟶ sliceOver a :=
  sliceOverCurry (pullback.lift (sliceOverUncurry (s ≫ pullback.fst _ _))
    (sliceOverUncurry (s ≫ pullback.snd _ _)) (slicePullbackFamily_comm f g a s)) (by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, sliceOverUncurry_fixed]
      · rw [Category.assoc, pullback.lift_snd, sliceOverUncurry_fixed])
/-- 復元した全錐の展開は、元の二成分をそのまま引き戻した全図式。 -/
lemma slicePullbackBackwardFamily_uncurry (s : A ⟶ slicePullbackDiagram f g a) :
    sliceOverUncurry (slicePullbackBackwardFamily f g a s) =
      pullback.lift (sliceOverUncurry (s ≫ pullback.fst _ _))
        (sliceOverUncurry (s ≫ pullback.snd _ _)) (slicePullbackFamily_comm f g a s) :=
  sliceOverUncurry_curry _ _
/-- 二成分の全錐の復元後の第一成分は、元の同じ全錐。 -/
lemma slicePullbackBackwardFamily_fst (s : A ⟶ slicePullbackDiagram f g a) :
    slicePullbackBackwardFamily f g a s ≫ sliceOverPostcomp a (pullback.fst f g) =
      s ≫ pullback.fst _ _ := by
  apply sliceOverUncurry_injective _
  rw [sliceOverUncurry_postcomp, slicePullbackBackwardFamily_uncurry, pullback.lift_fst]
/-- 二成分の全錐の復元後の第二成分も、元の同じ全錐。 -/
lemma slicePullbackBackwardFamily_snd (s : A ⟶ slicePullbackDiagram f g a) :
    slicePullbackBackwardFamily f g a s ≫ sliceOverPostcomp a (pullback.snd f g) =
      s ≫ pullback.snd _ _ := by
  apply sliceOverUncurry_injective _
  rw [sliceOverUncurry_postcomp, slicePullbackBackwardFamily_uncurry, pullback.lift_snd]
end SerrePositivity.InfinityCategories
