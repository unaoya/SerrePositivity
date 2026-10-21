module

public import SerrePositivity.KST.LocalizingInvariants.BinaryProjectionFibration

/-!
概要：元の点つき積の第一射影の基底変換は、元の点つき積である。
方針：二射影の外延性から実際の pullback 錐の普遍性を直接構成する。
規約：指定した積対象と射影を保持。使われ方：BF 積射影の各段の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.PointedProductProjection
variable {X Z : PointedSimplicialSet.{u}} (f : X ⟶ Z) (Y : PointedSimplicialSet.{u})

lemma condition : PointedObject.prodMap f (𝟙 Y) ≫ PointedObject.prodFst Z Y =
    PointedObject.prodFst X Y ≫ f := by
  simp only [PointedObject.prodMap, PointedObject.prodLift_fst]

def cone : PullbackCone (PointedObject.prodFst Z Y) f :=
  PullbackCone.mk (PointedObject.prodMap f (𝟙 Y)) (PointedObject.prodFst X Y) (condition f Y)

def isLimit : IsLimit (cone f Y) := by
  apply PullbackCone.IsLimit.mk (condition f Y)
    (fun s => PointedObject.prodLift s.snd (s.fst ≫ PointedObject.prodSnd Z Y))
  · intro s
    apply PointedObject.prod_hom_ext
    · simp only [PointedObject.prodMap, Category.assoc, PointedObject.prodLift_fst,
        PointedObject.prodLift_fst_assoc]
      exact s.condition.symm
    · simp only [PointedObject.prodMap, Category.assoc, PointedObject.prodLift_snd,
        PointedObject.prodLift_snd_assoc, Category.comp_id]
  · intro s
    exact PointedObject.prodLift_fst _ _
  · intro s m hm₁ hm₂
    apply PointedObject.prod_hom_ext
    · rw [PointedObject.prodLift_fst]
      exact hm₂
    · rw [PointedObject.prodLift_snd]
      have h := congrArg (fun a => a ≫ PointedObject.prodSnd Z Y) hm₁
      simpa only [Category.assoc, PointedObject.prodMap, PointedObject.prodLift_snd,
        Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants.PointedProductProjection
