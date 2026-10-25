module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationPreservation
public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitRestriction

/-!
概要：保存された小余積と幾何学的実現から保存された全小余極限を構成する。
方針：既存の存在と保存の生成定理を同じ元の余錐に適用する。
規約：幾何学的実現版の証明を複製せず、全余錐の同時保存を返す。
使われ方：P-11 の有限余極限・余積からの一般生成入口の共通部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小余積の存在と保存から同じ離散図式の保存された余錐を選べる。
方針：元の小余積の指定余錐に保存を適用する。
規約：元の余錐を変えず、その同じ像を使う。
使われ方：望遠鏡構成の小余積段階。 -/
lemma hasPreservedColimit_smallCoproduct {X Y : SSet.{u + 1}}
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : HasSmallCoproducts X) (hU : PreservesSmallCoproducts U)
    (I : Type u) (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X) :
    Ind.HasPreservedColimit U D := by
  obtain ⟨c, hc⟩ := hX I D
  exact ⟨c, hc, hU I D c hc⟩

/-- 概要：保存された小余積と実現から、元の任意の小図式の保存された余錐を構成する。
方針：既存の実現による存在と保存を同じ一つの余錐へ適用する。
規約：始域・像の余錐を別々に選ぶ存在条件へ弱めない。
使われ方：有限余極限・小余積による生成証明の最後の接続。 -/
lemma hasPreservedColimit_of_coproducts_preservedRealizations
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y)
    (hX : HasSmallCoproducts X) (hU : PreservesSmallCoproducts U)
    (hgeom : ∀ D : (SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ))) ⟶ X,
      Ind.HasPreservedColimit U D)
    (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X) :
    Ind.HasPreservedColimit U D := by
  have hge : HasSmallGeometricRealizations X := by
    intro F
    obtain ⟨c, hc, _⟩ := hgeom F
    exact ⟨c, hc⟩
  have hgp : PreservesSmallGeometricRealizations U := by
    intro F c hc
    exact (hgeom F).map_isColimit c hc
  obtain ⟨c, hc⟩ := hasSmallColimits_of_coproducts_geometricRealizations hX hge K D
  exact ⟨c, hc, preservesSmallColimits_of_coproducts_geometricRealizations
    hX U hU hgp K D c hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
