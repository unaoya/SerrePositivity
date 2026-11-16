module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationRightKanConeComparison

/-!
概要：各引き戻し篩での降下から、元の二段分解の指定右 Kan 条件を得る。
方針：全頂点を元の中間射に戻し、同じ指定局所錐の極限性の同値を適用する。
  文献対応：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の降下の合成。
規約：係数には準圏性だけを仮定する。大域の極限の存在は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C} {E : SSet.{u + 1}} [Quasicategory E]

/-- 各引き戻し篩での元の降下は、同じ三角形の指定余単位による右 Kan 延長を与える。 -/
lemma sieveFactorization_isRightKanExtension (R S : Sieve U) (F : Presheaf C E)
    (hF : ∀ t : sieveCategory R, IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) :
    IsRightKanExtension (nerveMap (sieveFactorizationRightKanFunctor R S))
      (nerveMap (sieveFactorizationRightKanSource R S) ≫ sieveFactorizationRightKanCoefficient F)
      (nerveMap (sieveFactorizationRightKanTarget R) ≫ sieveFactorizationRightKanCoefficient F)
      (sieveFactorizationRightKanCounitHomotopy R S F) := by
  intro v
  obtain ⟨a, rfl⟩ := (nerveEquiv (C := AsSmall.{u + 1} (sieveCategory R)ᵒᵖ)).symm.surjective v
  let t : sieveCategory R := (AsSmall.down.obj a).unop
  have ha : AsSmall.up.obj (Opposite.op t) = a := by cases a; rfl
  rw [← ha]
  exact ⟨sieveFactorizationRightKanTransport R S t F,
    (sieveFactorizationRightKanTransport_isLimit_iff R S t F).mpr (hF t)⟩

end SerrePositivity.InfinityCategories.Sheaves
