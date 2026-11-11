module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CardinalChangeBound
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：μ-small な形状の全単体を、同じ μ で数える。
方針：各非退化単体の有限部分複体で各次数を被覆し、正則性で全次数を合計する。
規約：μ は非可算正則。非退化単体の小ささと各次数の小ささを同一視しない。
使われ方：μ-small 形状の単体圏と weighted 極限の大きさの評価。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 正則無限 μ について、μ-small な形状の各次数の単体も μ 個未満。 -/
lemma hasCardinalLT_simplices_of_isKappaSmall {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) (n : ℕ) : HasCardinalLT (K _⦋n⦌) μ := by
  have hN : HasCardinalLT K.N μ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  have hU : HasCardinalLT (⋃ s : K.N, s.subcomplex.obj (Opposite.op ⦋n⦌)) μ :=
    hasCardinalLT_iUnion _ hN (fun s ↦ by
      have : Finite ((s.subcomplex : SSet.{u}) _⦋n⦌) := inferInstance
      exact hasCardinalLT_of_finite ((s.subcomplex : SSet.{u}) _⦋n⦌) μ
        (Cardinal.IsRegular.aleph0_le (Fact.out : μ.IsRegular)))
  have htop : (⋃ s : K.N, s.subcomplex.obj (Opposite.op ⦋n⦌)) = Set.univ := by
    have he := congrArg (fun A : K.Subcomplex ↦ A.obj (Opposite.op ⦋n⦌))
      (N.iSup_subcomplex_eq_top K)
    simpa only [Subfunctor.iSup_obj, Subfunctor.top_obj] using he
  exact hU.of_surjective (fun s ↦ s.val) (fun s ↦
    ⟨⟨s, by rw [htop]; trivial⟩, rfl⟩)

/-- 非可算正則 μ について、全次数を合わせた元の単体の型も μ-small。 -/
lemma hasCardinalLT_allSimplices_of_isKappaSmall {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) :
    HasCardinalLT K.S μ := by
  have hNat : HasCardinalLT (ULift.{u} ℕ) μ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hμ
  have hAll : HasCardinalLT (Σ n : ULift.{u} ℕ, K _⦋n.down⦌) μ :=
    hasCardinalLT_sigma _ μ hNat (fun n ↦ hasCardinalLT_simplices_of_isKappaSmall hK n.down)
  exact hAll.of_injective (fun s ↦ ⟨ULift.up s.dim, s.simplex⟩) (by
    intro s t h
    cases s
    cases t
    cases h
    rfl)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
