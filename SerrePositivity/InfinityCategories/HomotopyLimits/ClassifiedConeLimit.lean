module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ClassifiedConeLift
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationConeLimit

/-!
概要：元の前層が極限へ送る底の極限錐を、小さい全空間自身の極限錐へ持ち上げる。
方針：同じ指定図式を固定した全延長空間の可縮性と相対境界充填を使う。
規約：図式と全錐の射影を厳密に保持し、底の極限存在は明示する。
使われ方：有限積保存する前層の元の圏の有限積の存在。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の底の極限錐をその像も極限となるよう持ち上げれば、同じ全錐は全空間でも極限。 -/
lemma classifiedCone_isLimit
    {K B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {d : K ⟶ smallLeftUnstraightening F} (a : JoinCone d)
    (ha : IsLimitCone (mapJoinCone (smallLeftUnstraighteningProjection F) a))
    (hF : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1}
      (mapJoinCone (smallLeftUnstraighteningProjection F) a)))) : IsLimitCone a :=
  isLimitCone_of_leftFibration_extension (smallLeftUnstraighteningProjection F) a ha
    (classifiedConeExtension_isContractibleKan
      (mapJoinCone (smallLeftUnstraighteningProjection F) a) F hF d rfl)

/-- 元の図式と底の同じ極限錐を厳密に保つ、全空間内の極限錐が存在する。 -/
lemma exists_classifiedLimitCone
    {K B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (d : K ⟶ smallLeftUnstraightening F)
    (c : JoinCone (d ≫ smallLeftUnstraighteningProjection F)) (hc : IsLimitCone c)
    (hF : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c))) :
    ∃ a : JoinCone d, IsLimitCone a ∧
      mapJoinCone (smallLeftUnstraighteningProjection F) a = c := by
  obtain ⟨a, ha⟩ := exists_classifiedConeLift c F hF d rfl
  have he : mapJoinCone (smallLeftUnstraighteningProjection F) a = c := Subtype.ext ha
  refine ⟨a, ?_, he⟩
  apply classifiedCone_isLimit F a
  · rwa [he]
  · rwa [he]

/-- 有限積保存する元の前層の全空間には、底に存在する同じ有限積の持ち上げが存在。 -/
lemma hasLimit_smallLeftUnstraightening_of_finiteProducts
    {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hF : PreservesFiniteProductsFromSmallSource F)
    {J : Type u} [Finite J] (d : nerve (Discrete J) ⟶ smallLeftUnstraightening F)
    (hc : HasLimit (d ≫ smallLeftUnstraighteningProjection F)) : HasLimit d := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨a, ha, _⟩ := exists_classifiedLimitCone F d c hc (hF.map_isLimit hc)
  exact ⟨a, ha⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
