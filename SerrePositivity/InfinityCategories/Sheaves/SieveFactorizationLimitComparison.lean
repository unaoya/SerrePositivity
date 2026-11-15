module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationRightKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NerveTriangleLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.AsSmallCoefficientCone

/-!
概要：元の各引き戻し篩の降下から、二段分解上の同じ錐と元の篩の錐を比較する。
方針：既検証の指定右 Kan 条件を同じ通常の三角形へ適用し、AsSmall の表示から戻す。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の交叉篩の降下。
規約：任意の準圏係数。極限の存在を追加仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 元の二段分解の三角形は、AsSmall 表示でも同じ全錐の後合成を与える。 -/
lemma sieveFactorization_asSmall_postCone (R S : Sieve U) :
    (Cone.postcompose (sieveFactorizationRightKanCounit R S)).obj
      ((asSmallCone (sieveCone R)).whisker (sieveFactorizationRightKanFunctor R S)) =
      asSmallCone (sieveFactorizationCone R S) := by
  change Cone.mk (AsSmall.up.obj (Opposite.op U)) _ =
    Cone.mk (AsSmall.up.obj (Opposite.op U)) _
  congr 1
  apply NatTrans.ext
  funext B
  have h := NatTrans.congr_app (sieveFactorizationCone_triangle R S) (AsSmall.down.obj B)
  exact congrArg ((AsSmall.up : Cᵒᵖ ⥤ AsSmall.{u + 1} Cᵒᵖ).map) h.symm

/-- 元の指定余単位は、通常の三角形から組み立てた同じ指定ホモトピーである。 -/
lemma sieveFactorization_whiskerCounit (R S : Sieve U)
    {E : SSet.{u + 1}} (F : Presheaf C E) :
    nerveWhiskerCoefficientCounitHomotopy (sieveFactorizationRightKanFunctor R S)
      (sieveFactorizationRightKanCounit R S) (sieveFactorizationRightKanCoefficient F) =
      sieveFactorizationRightKanCounitHomotopy R S F := by
  apply SSet.RelativeMorphism.Homotopy.ext
  rfl

/-- 各引き戻し篩での降下があれば、元の篩と二段分解上の同じ全錐の極限性は同値。 -/
lemma sieveFactorizationCone_isLimit_iff (R S : Sieve U)
    {E : SSet.{u + 1}} [Quasicategory E] (F : Presheaf C E)
    (hF : ∀ t : sieveCategory R, IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) :
    IsLimitCone (restrictionCone F R) ↔
      IsLimitCone (((nerveCone (sieveFactorizationCone R S)).ulift).postcomp F) := by
  have hr := sieveFactorization_isRightKanExtension R S F hF
  rw [← sieveFactorization_whiskerCounit R S F] at hr
  have h := nerveConeWhiskerPostcompose_isLimit_iff_arbitrary
    (sieveFactorizationRightKanFunctor R S) (asSmallCone (sieveCone R))
    (sieveFactorizationRightKanCounit R S) (sieveFactorizationRightKanCoefficient F) hr
  rw [sieveFactorization_asSmall_postCone] at h
  exact (isLimitCone_asSmallCoefficient_iff (sieveCone R) F).symm.trans
    (h.trans (isLimitCone_asSmallCoefficient_iff (sieveFactorizationCone R S) F))

end SerrePositivity.InfinityCategories.Sheaves
