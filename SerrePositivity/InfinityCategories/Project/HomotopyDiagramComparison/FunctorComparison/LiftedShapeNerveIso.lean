module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SectionsShapeBaseIso

/-!
概要：三形状の nerve の宇宙の持ち上げを既存の切断比較が使う標準の底へ同型で移す。
方針：AsSmall の重複を取り除き、離散対象の持ち上げを直接対応させる。
規約：単なる圏同値ではなく厳密な逆関手から単体集合の同型を構成する。
使われ方：HTT 4.2.4.1 の豊穣係数と coherent な錐の切断比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：小圏の二つの厳密な逆関手は nerve の厳密な同型を与える。
方針：各合成可能射列に後合成し、逆関手の等式で両方向の往復を示す。
規約：二圏の対象と射の宇宙は共通。
使われ方：HTT 4.2.4.1 の持ち上げた三形状の底の同定。 -/
def nerveIsoOfStrictInverse {A B : Type u} [SmallCategory A] [SmallCategory B]
    (F : A ⥤ B) (G : B ⥤ A) (hFG : F ⋙ G = 𝟭 A) (hGF : G ⋙ F = 𝟭 B) :
    nerve A ≅ nerve B where
  hom := nerveMap F
  inv := nerveMap G
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ F) ⋙ G = σ
    simpa only [Functor.assoc, Functor.comp_id] using congrArg (fun H ↦ σ ⋙ H) hFG
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro σ
    change (σ ⋙ G) ⋙ F = σ
    simpa only [Functor.assoc, Functor.comp_id] using congrArg (fun H ↦ σ ⋙ H) hGF

/-- 概要：離散圏の nerve の持ち上げは持ち上げた離散対象の nerve と同型。
方針：AsSmall へ移した後で離散対象の ULift を交換する厳密な逆関手を使う。
規約：対象型の有限性を要求しない。
使われ方：HTT 4.2.4.1 の積の切断比較の底のサイズの調整。 -/
def liftedDiscreteNerveIso (J : Type u) :
    (SSet.uliftFunctor.{v, u}).obj (nerve (Discrete J)) ≅
      nerve (Discrete (ULift.{v, u} J)) := by
  let F : AsSmall.{v} (Discrete J) ⥤ Discrete (ULift.{v, u} J) :=
    AsSmall.down ⋙ Discrete.functor (fun j : J ↦ Discrete.mk (ULift.up j))
  let G : Discrete (ULift.{v, u} J) ⥤ AsSmall.{v} (Discrete J) :=
    Discrete.functor (fun j : ULift.{v, u} J ↦ AsSmall.up.obj (Discrete.mk j.down))
  have hFG : F ⋙ G = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ ?_)
    apply ULift.ext
    exact Subsingleton.elim _ _
  have hGF : G ⋙ F = 𝟭 _ :=
    CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso (Discrete J) ≪≫ nerveIsoOfStrictInverse F G hFG hGF

/-- 概要：AsSmall で持ち上げた零宇宙の圏の nerve をさらに持ち上げても一回の持ち上げと同型。
方針：二回の up・down を一回にまとめる厳密な逆関手を使う。
規約：WalkingCospan と自然数の逆順の圏の双方に適用する。
使われ方：HTT 4.2.4.1 の引き戻しと塔の切断比較の底のサイズの調整。 -/
def liftedAsSmallNerveIso (J : Type) [SmallCategory J] :
    (SSet.uliftFunctor.{v, u}).obj (nerve (AsSmall.{u} J)) ≅
      nerve (AsSmall.{max u v} J) := by
  let F : AsSmall.{v} (AsSmall.{u} J) ⥤ AsSmall.{max u v} J :=
    AsSmall.down ⋙ AsSmall.down ⋙ AsSmall.up
  let G : AsSmall.{max u v} J ⥤ AsSmall.{v} (AsSmall.{u} J) :=
    AsSmall.down ⋙ AsSmall.up ⋙ AsSmall.up
  have hFG : F ⋙ G = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hGF : G ⋙ F = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso (AsSmall.{u} J) ≪≫ nerveIsoOfStrictInverse F G hFG hGF

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
