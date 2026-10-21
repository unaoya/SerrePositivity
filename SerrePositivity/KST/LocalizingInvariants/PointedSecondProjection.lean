module

public import SerrePositivity.KST.LocalizingInvariants.PointedProductProjection

/-!
概要：点つき積の第二射影の基底変換の元の積による表示と fibration 性。
方針：第二射影の fibration 性は対称性で第一射影へ帰着し、二射影で普遍性を検証する。
規約：固定した第一因子を保持。使われ方：graph の四角形を得る貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants

lemma snd_projection_fibration (X Y : SSet.{u}) [KanComplex X] :
    Fibration (CartesianMonoidalCategory.snd X Y) := by
  have : Fibration (CartesianMonoidalCategory.fst Y X) := Binary.projection_fibration _ _
  rw [← CartesianMonoidalCategory.braiding_hom_fst X Y]
  infer_instance

namespace PointedSecondProjection
variable {X Z : PointedSimplicialSet.{u}} (f : X ⟶ Z) (Y : PointedSimplicialSet.{u})

lemma condition : PointedObject.prodMap (𝟙 Y) f ≫ PointedObject.prodSnd Y Z =
    PointedObject.prodSnd Y X ≫ f := by
  simp only [PointedObject.prodMap, PointedObject.prodLift_snd]

def cone : PullbackCone (PointedObject.prodSnd Y Z) f :=
  PullbackCone.mk (PointedObject.prodMap (𝟙 Y) f) (PointedObject.prodSnd Y X) (condition f Y)

def isLimit : IsLimit (cone f Y) := by
  apply PullbackCone.IsLimit.mk (condition f Y)
    (fun s => PointedObject.prodLift (s.fst ≫ PointedObject.prodFst Y Z) s.snd)
  · intro s
    apply PointedObject.prod_hom_ext
    · simp only [PointedObject.prodMap, Category.assoc, PointedObject.prodLift_fst,
        Category.comp_id]
    · simp only [PointedObject.prodMap, Category.assoc, PointedObject.prodLift_snd,
        PointedObject.prodLift_snd_assoc]
      exact s.condition.symm
  · intro s
    exact PointedObject.prodLift_snd _ _
  · intro s m hm₁ hm₂
    apply PointedObject.prod_hom_ext
    · rw [PointedObject.prodLift_fst]
      have ht := congrArg (fun a => a ≫ PointedObject.prodFst Y Z) hm₁
      simpa only [Category.assoc, PointedObject.prodMap, PointedObject.prodLift_fst,
        Category.comp_id] using ht
    · rw [PointedObject.prodLift_snd]
      exact hm₂

end PointedSecondProjection
end SerrePositivity.KST.LocalizingInvariants
