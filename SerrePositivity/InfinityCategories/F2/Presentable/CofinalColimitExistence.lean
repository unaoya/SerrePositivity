module

public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullyFaithfulPrecompositionColimits

/-!
概要：全余錐空間の同値による余極限の存在の比較。
方針：制限先の始対象を同値の逆関手で戻す。
規約：元の図式への余極限の存在を結論する。
使われ方：離散次数ファイバーの小余積から左 Kan 局所余極限を構成する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全余錐制限が同値なら、制限後の余極限から元の余極限が存在する。
方針：制限後の始対象を同じ同値の逆で戻す。
規約：元の形状の単射性は要求しない。
使われ方：小さい cofinal な図式からの存在の移送。 -/
lemma hasColimit_of_sliceUnderRestrict_equivalence
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) (F : B ⟶ X)
    (he : IsQCatEquivalence (sliceUnderRestrict F i)) (hF : HasColimit (i ≫ F)) :
    HasColimit F := by
  obtain ⟨c, hc⟩ := hF
  let e := he.choose
  exact ⟨e.inv.app _ c, (e.symm.isInitialVertex_iff c).mp hc⟩

/-- 概要：right cofinal な制限後に余極限があれば、元の図式も余極限を持つ。
方針：同じ全余錐制限の同値性により存在を戻す。
規約：指定標的の quasicategory 性のみを要求する。
使われ方：bar の次数ごとの小余積による左 Kan 延長の構成。 -/
lemma hasColimit_of_rightCofinalRestriction
    {A B X : SSet.{u}} [Quasicategory B] [Quasicategory X]
    (i : A ⟶ B) (hi : IsRightCofinal i) (F : B ⟶ X) (hF : HasColimit (i ≫ F)) :
    HasColimit F :=
  hasColimit_of_sliceUnderRestrict_equivalence i F
    (Ind.sliceUnderRestrict_equivalence_of_rightCofinal i hi F) hF

/-- 概要：充満忠実な前合成による制限後の余極限から元の余極限が存在する。
方針：全余錐制限の同値性を使う。
規約：前合成の本質的全射性を仮定しない。
使われ方：単体圏で展開した図式からの元の小余極限の回収。 -/
lemma hasColimit_of_fullyFaithfulPrecomposition
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B)
    (hi : IsFullyFaithful ((pre i).app X)) (F : B ⟶ X) (hF : HasColimit (i ≫ F)) :
    HasColimit F :=
  hasColimit_of_sliceUnderRestrict_equivalence i F
    (HomotopyLimits.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre i hi F) hF

end SerrePositivity.InfinityCategories.F2.Presentable
