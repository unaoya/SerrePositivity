module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso

/-!
# 対象宇宙の異なる次数関手と comma nerve の引き戻し

概要：Hom 宇宙が同じでも対象宇宙が異なる元の関手の nerve 引き戻しを構成する。
方針：対象だけの ULift を厳密に往復し、通常の nerve の極限保存から移送する。
規約：元の関手・comma の射・全単体の作用を保持する。
使われ方：元の sourceFrameHom の反対要素圏の次数モデル。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MixedNerveCostructuredPullback
open CategoryTheory Limits _root_.SerrePositivity.InfinityCategories
attribute [local instance] uliftCategory
variable {I : Type u} [Category.{u + 1} I]
  {C : Type (u + 1)} [Category.{u + 1} C] (A : I ⥤ C) (c : C)

abbrev lifted : ULift.{u + 1} I ⥤ C := ULift.downFunctor ⋙ A

def toLifted : CostructuredArrow A c ⥤ CostructuredArrow (lifted A) c where
  obj s := { left := ⟨s.left⟩, right := ⟨⟨⟩⟩, hom := s.hom }
  map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)

def fromLifted : CostructuredArrow (lifted A) c ⥤ CostructuredArrow A c where
  obj s := { left := ULift.down s.left, right := ⟨⟨⟩⟩, hom := s.hom }
  map f := CostructuredArrow.homMk f.left (CostructuredArrow.w f)

def commaNerveIso : nerve (CostructuredArrow A c) ≅
    nerve (CostructuredArrow (lifted A) c) where
  hom := nerveMap (toLifted A c)
  inv := nerveMap (fromLifted A c)
  hom_inv_id := rfl
  inv_hom_id := rfl

def sourceNerveIso : nerve I ≅ nerve (ULift.{u + 1} I) where
  hom := { app _ := ↾fun σ => σ ⋙ ULift.upFunctor
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ ULift.downFunctor
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def baseMap : nerve I ⟶ nerve C where
  app _ := ↾fun σ => σ ⋙ A
  naturality _ _ _ := rfl

def projection : nerve (CostructuredArrow A c) ⟶ nerve I where
  app _ := ↾fun σ => σ ⋙ CostructuredArrow.proj A c
  naturality _ _ _ := rfl

lemma isPullback : IsPullback (nerveMap (CostructuredArrow.toOver A c))
    (projection A c) (nerveMap (Over.forget c)) (baseMap A) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveCostructuredArrow_isPullback (lifted A) c).of_iso
    (commaNerveIso A c).symm (Iso.refl _) (sourceNerveIso (I := I)).symm (Iso.refl _)
    (by rfl) (by rfl) (by rfl) (by rfl)

def pullbackIso : nerve (CostructuredArrow A c) ≅
    pullback (baseMap A) (nerveMap (Over.forget c)) :=
  (isPullback A c).flip.isoPullback

lemma pullbackIso_source : (pullbackIso A c).hom ≫ pullback.fst _ _ = projection A c :=
  (isPullback A c).flip.isoPullback_hom_fst

lemma pullbackIso_over : (pullbackIso A c).hom ≫ pullback.snd _ _ =
    nerveMap (CostructuredArrow.toOver A c) :=
  (isPullback A c).flip.isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MixedNerveCostructuredPullback
