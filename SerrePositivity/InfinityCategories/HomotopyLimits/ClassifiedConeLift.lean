module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaElementsConeRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFibration
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTrivialComparison

/-!
概要：像が極限となる錐上で、指定した小さい全空間の底図式を厳密に延長する。
方針：元の切断制限の同値性を自明 Kan 性へ強め、元の底図式を固定した fiber を取る。
規約：同じ底上の全写像を持ち上げ、全高次の選択空間も可縮と示す。
使われ方：P_Σ の元の圏での有限積構成の存在部分。全空間での極限性は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ切断制限が同値なら、元の底図式を固定した全錐の延長空間は可縮 Kan。 -/
lemma coneExtension_isContractibleKan_of_restriction_equivalence
    {K E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {D : K ⟶ B} (c : JoinCone D)
    (h : IsQCatEquivalence (leftFibrationConeRestriction p c))
    (d : K ⟶ E) (hd : d ≫ p = D) :
    IsContractibleKan (relativeFunctorExtensionSpace p c.val
      (joinInr (Δ[0] : SSet.{u}) K) d (hd.trans c.property.symm)) := by
  let i := joinInr (Δ[0] : SSet.{u}) K
  have he : IsQCatEquivalence (eqToHom (congrArg (relativeFunctorSpace p) c.property)) :=
    (qCatEquivalenceOfIso (eqToIso
      (congrArg (relativeFunctorSpace p) c.property))).isQCatEquivalence
  have hr : IsQCatEquivalence (relativeFunctorPre p c.val i) :=
    he.cancel_right h
  have := trivialKanFibration_of_leftFibration_of_isQCatEquivalence
    (relativeFunctorPre p c.val i) hr
  exact vertexFiber_isContractibleKan _ _

/-- 像が極限となる元の錐の、指定底図式を固定した小さい全空間への延長空間は可縮。 -/
lemma classifiedConeExtension_isContractibleKan
    {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hc : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)))
    (d : K ⟶ smallLeftUnstraightening F)
    (hd : d ≫ smallLeftUnstraighteningProjection F = D) :
    IsContractibleKan (relativeFunctorExtensionSpace (smallLeftUnstraighteningProjection F)
      c.val (joinInr (Δ[0] : SSet.{u}) K) d (hd.trans c.property.symm)) :=
  coneExtension_isContractibleKan_of_restriction_equivalence _ c
    (smallLeftConeRestriction_isQCatEquivalence_of_map_isLimit c F hc) d hd

/-- 指定した元の底図式を保つ、同じ小さい全空間内の全錐が存在する。 -/
lemma exists_classifiedConeLift
    {K B : SSet.{u}} {D : K ⟶ B} (c : JoinCone D)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (hc : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)))
    (d : K ⟶ smallLeftUnstraightening F)
    (hd : d ≫ smallLeftUnstraighteningProjection F = D) :
    ∃ a : JoinCone d, a.val ≫ smallLeftUnstraighteningProjection F = c.val := by
  have h := classifiedConeExtension_isContractibleKan c F hc d hd
  obtain ⟨v⟩ := h.nonempty
  let W := (relativeFunctorExtensionSpaceVertexEquiv _ _ _ d
    (hd.trans c.property.symm)).symm v
  exact ⟨⟨W.val, W.property.2⟩, W.property.1⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
