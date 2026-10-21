module

public import SerrePositivity.InfinityCategories.F1.CocartesianCellAttachmentPullbacks
public import SerrePositivity.InfinityCategories.F1.CocartesianPullbackCoreFibration
public import SerrePositivity.InfinityCategories.F1.KanFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.IntervalDiagramRestrictionFibration
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftLifting

/-!
概要：セル付加後の元の Hom から既存部分への両側の制限は Kan fibration。
方針：単射な境界包含の pushout の単射性を、元の Hom 制限の充填性へ移す。
規約：境界から既存部分への貼付け写像には単射性を要求しない。
使われ方：骨格列の元の Hom の matching map と固定境界の延長空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 単射による元の native core 制限は、分類先の宇宙でも Kan fibration。 -/
lemma cocartesianPullbackNativeLiftPre_fibration {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q]
    {a b : Over B} (f : a ⟶ b) [Mono f.left] :
    Fibration (cocartesianPullbackNativeLiftPre p q f) := by
  have : Fibration (quasicategoryCoreMap (cocartesianPullbackNativePre p q f)) :=
    core_cocartesianPullbackNativePre_fibration p q f
  exact fibration_uliftFunctor_map _

variable {B : SSet.{u}} {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left) [Mono f.left]

include hp in
/-- 任意のセル貼付け後の元の全 Hom の既存部分への制限は Kan fibration。 -/
lemma cocartesianCellAttachment_nativeRestriction_fibration
    {E F : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (q : F ⟶ B) [CocartesianFibration q] :
    Fibration (cocartesianPullbackNativeLiftPre p q j) := by
  have : Mono j.left := Adhesive.mono_of_isPushout_of_mono_left hp
  exact cocartesianPullbackNativeLiftPre_fibration p q j

include hp in
/-- 同じセル貼付け後の分類先の既存部分への区間 Hom 制限も Kan fibration。 -/
lemma cocartesianCellAttachment_intervalRestriction_fibration
    {X : SSet.{u + 1}} [Quasicategory X]
    (P Q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) :
    Fibration (intervalDiagramOverPre P Q (uliftOverMorphism j)) := by
  have : Mono j.left := Adhesive.mono_of_isPushout_of_mono_left hp
  have : Mono (uliftOverMorphism.{u, u + 1} j).left :=
    SimplicialModel.UniverseLift.mono_map j.left
  exact intervalDiagramOverPre_fibration P Q (uliftOverMorphism j)

end SerrePositivity.InfinityCategories
