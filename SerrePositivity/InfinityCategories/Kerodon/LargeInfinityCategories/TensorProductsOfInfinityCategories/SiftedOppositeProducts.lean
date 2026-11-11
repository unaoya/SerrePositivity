module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.OppositeDiagramReturn

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.BinaryDiscreteShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedCoproductCriterion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex

/-!
概要：元の全有限積の存在から、反対 ∞ 圏の sifted 性を得る。
方針：空積で非空性を得て、元の二点形状を反転し同じ二項余積を構成する。
規約：全有限積の存在は実際の全錐の存在で量化し、通常のホモトピー圏で代用しない。
使われ方：P_Σ 前層の元の小さい元の圏の sifted 性。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 元の同型形状への再添字で得た極限から、元の同じ図式の極限を回収する。 -/
lemma hasLimit_of_iso_reindex {A K X : SSet.{u}} (e : A ≅ K) (d : K ⟶ X)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (e.hom ≫ d)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d := by
  obtain ⟨c, hc⟩ := h
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (e.inv ≫ (e.hom ≫ d)) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c e.inv, (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso c e.inv).mpr hc⟩
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
    (h : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity X.op := by
  obtain ⟨c, _⟩ := h PEmpty (emptyDiscreteDiagram X)
  have h₀ : Nonempty (X.op _⦋0⦌) := ⟨SSet.opObjEquiv.symm c.vertex⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.isSiftedInfinity_of_hasBinaryCoproducts X.op h₀
  intro d
  let K := (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})
  let q : K.op ⟶ X := SSet.opFunctor.map d ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
  let e : nerve (Discrete (ULift.{u} Bool)) ≅ K.op :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteNerveOppositeIso _).symm ≪≫
      ((SSet.opFunctor).mapIso _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.binaryDiscreteNerveIso).symm
  obtain ⟨a, ha⟩ := hasLimit_of_iso_reindex e q (h _ (e.hom ≫ q))
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone_restrict a
    (SSet.opFunctorCompOpFunctorIso.app K).inv).mp ha
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.opFunctorCompOpFunctorIso.app K).inv ≫
      SSet.opFunctor.map q) :=
    ⟨a.reverseCocone.restrict (SSet.opFunctorCompOpFunctorIso.app K).inv, hc⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.opFunctorCompOpFunctorIso.app K).inv ≫
    SSet.opFunctor.map (SSet.opFunctor.map d ≫
      (SSet.opFunctorCompOpFunctorIso.app X).hom)) at hc'
  rwa [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.oppositeDiagram_double_return d] at hc'

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
