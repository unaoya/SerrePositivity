module

public import SerrePositivity.InfinityCategories.HomotopyLimits.BinaryDiscreteShape
public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedCoproductCriterion
public import SerrePositivity.InfinityCategories.F2.FunctorVertexConeReindex

/-!
概要：元の全有限積の存在から、反対 ∞ 圏の sifted 性を得る。
方針：空積で非空性を得て、元の二点形状を反転し同じ二項余積を構成する。
規約：全有限積の存在は実際の全錐の存在で量化し、通常のホモトピー圏で代用しない。
使われ方：P_Σ 前層の元の小さい元の圏の sifted 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の同型形状への再添字で得た極限から、元の同じ図式の極限を回収する。 -/
lemma hasLimit_of_iso_reindex {A K X : SSet.{u}} (e : A ≅ K) (d : K ⟶ X)
    (h : HasLimit (e.hom ≫ d)) : HasLimit d := by
  obtain ⟨c, hc⟩ := h
  have h' : HasLimit (e.inv ≫ (e.hom ≫ d)) :=
    ⟨F2.restrictJoinCone c e.inv, (F2.isLimitCone_restrict_iff_of_isIso c e.inv).mpr hc⟩
  simpa only [Iso.inv_hom_id_assoc] using h'

/-- 空の離散 nerve から元の単体集合への、同じ空図式。 -/
def emptyDiscreteDiagram (X : SSet.{u}) : nerve (Discrete PEmpty.{u + 1}) ⟶ X where
  app _ := ↾fun s => PEmpty.elim (s.obj 0).as
  naturality {_ _} _ := by
    apply ConcreteCategory.hom_ext
    intro s
    exact PEmpty.elim (s.obj 0).as

/-- 全有限積を持つ元の ∞ 圏の反転は、元の二項余積により sifted。 -/
lemma isSiftedInfinity_op_of_hasFiniteProducts (X : SSet.{u}) [Quasicategory X]
    (h : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ X), HasLimit p) :
    IsSiftedInfinity X.op := by
  obtain ⟨c, _⟩ := h PEmpty (emptyDiscreteDiagram X)
  have h₀ : Nonempty (X.op _⦋0⦌) := ⟨SSet.opObjEquiv.symm c.vertex⟩
  apply isSiftedInfinity_of_hasBinaryCoproducts X.op h₀
  intro d
  let K := (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})
  let q : K.op ⟶ X := SSet.opFunctor.map d ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  let e : nerve (Discrete (ULift.{u} Bool)) ≅ K.op :=
    (discreteNerveOppositeIso _).symm ≪≫
      ((SSet.opFunctor).mapIso binaryDiscreteNerveIso).symm
  obtain ⟨a, ha⟩ := hasLimit_of_iso_reindex e q (h _ (e.hom ≫ q))
  have hc := (isLimitCone_iff_reverseCocone_restrict a
    (SSet.opFunctorCompOpFunctorIso.app K).inv).mp ha
  have hc' : HasColimit ((SSet.opFunctorCompOpFunctorIso.app K).inv ≫
      SSet.opFunctor.map q) :=
    ⟨a.reverseCocone.restrict (SSet.opFunctorCompOpFunctorIso.app K).inv, hc⟩
  change HasColimit ((SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (SSet.opFunctor.map d ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom)) at hc'
  rwa [oppositeDiagram_double_return d] at hc'

end SerrePositivity.InfinityCategories.HomotopyLimits
