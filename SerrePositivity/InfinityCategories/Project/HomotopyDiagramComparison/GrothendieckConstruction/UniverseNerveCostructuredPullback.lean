module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso

/-!
概要：元の次数関手の comma nerve を任意の共通上限宇宙の引き戻しと同定する。
方針：対象だけの ULift の順逆と元の nerve の極限保存を使う。
規約：元の対象・射・全単体を保持する。
使われ方：一般モデル圏の実屋根の次数モデル。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback
open CategoryTheory Limits _root_.SerrePositivity.InfinityCategories
attribute [local instance] uliftCategory
variable {I : Type u} [Category.{max u w} I]
  {C : Type (max u w)} [Category.{max u w} C] (A : I ⥤ C) (c : C)

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
abbrev lifted : ULift.{max u w} I ⥤ C := ULift.downFunctor ⋙ A

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def toLifted : CostructuredArrow A c ⥤ CostructuredArrow (lifted.{u, w} A) c where
  obj s := { left := ⟨s.left⟩, right := ⟨⟨⟩⟩, hom := s.hom }
  map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def fromLifted : CostructuredArrow (lifted.{u, w} A) c ⥤ CostructuredArrow A c where
  obj s := { left := ULift.down s.left, right := ⟨⟨⟩⟩, hom := s.hom }
  map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def commaNerveIso : nerve (CostructuredArrow A c) ≅
    nerve (CostructuredArrow (lifted.{u, w} A) c) where
  hom := nerveMap (toLifted.{u, w} A c)
  inv := nerveMap (fromLifted.{u, w} A c)
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def sourceNerveIso : nerve I ≅ nerve (ULift.{max u w} I) where
  hom := { app _ := ↾fun σ => σ ⋙ ULift.upFunctor
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ ULift.downFunctor
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def baseMap : nerve I ⟶ nerve C where
  app _ := ↾fun σ => σ ⋙ A
  naturality _ _ _ := rfl

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def projection : nerve (CostructuredArrow A c) ⟶ nerve I where
  app _ := ↾fun σ => σ ⋙ CostructuredArrow.proj A c
  naturality _ _ _ := rfl

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
lemma isPullback : IsPullback (nerveMap (CostructuredArrow.toOver A c))
    (projection.{u, w} A c) (nerveMap (Over.forget c)) (baseMap.{u, w} A) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveCostructuredArrow_isPullback (lifted.{u,
    w} A) c).of_iso
    (commaNerveIso.{u, w} A c).symm (Iso.refl _) (sourceNerveIso.{u, w} (I := I)).symm (Iso.refl _)
    (by rfl) (by rfl) (by rfl) (by rfl)

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
def pullbackIso : nerve (CostructuredArrow A c) ≅
    pullback (baseMap.{u, w} A) (nerveMap (Over.forget c)) :=
  (isPullback.{u, w} A c).flip.isoPullback

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
lemma pullbackIso_source : (pullbackIso.{u, w} A c).hom ≫ pullback.fst _ _ = projection.{u, w}
  A c :=
  (isPullback.{u, w} A c).flip.isoPullback_hom_fst

/-- 概要：元の次数関手の comma と nerve の同じ表示を任意上限で回収する。
方針：元の対象だけの up・down と同じ全射列を評価する。
規約：元の全作用素。使われ方：実屋根の次数引き戻しの同定。 -/
lemma pullbackIso_over : (pullbackIso.{u, w} A c).hom ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.toOver A c) :=
  (isPullback.{u, w} A c).flip.isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseNerveCostructuredPullback
