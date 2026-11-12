module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallSubcomplexCovers
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：正則 κ に対して κ-small な単体集合の直積も κ-small。
方針：元の両因子の非退化単体の対で添字付けた有限部分複体による被覆を使う。
規約：κ-small 性と被覆の濃度判定は F2N-1 の提供済み宣言を使う。
使われ方：κ-small な円柱上のホモトピーの相対因子分解。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 両因子の元の非退化単体が生成する有限な直積部分複体。 -/
def smallProductPiece (K L : SSet.{u}) (s : K.N × L.N) : (K ⊗ L).Subcomplex :=
  (Subcomplex.ofSimplex s.1.simplex).prod (Subcomplex.ofSimplex s.2.simplex)

instance smallProductPiece_finite (K L : SSet.{u}) (s : K.N × L.N) :
    (smallProductPiece K L s).toSSet.Finite := by
  dsimp only [smallProductPiece]
  rw [Subcomplex.ofSimplexProd_eq_range]
  infer_instance

/-- 元の非退化単体の対の直積部分複体は、元の直積の全単体を覆う。 -/
lemma iSup_smallProductPiece (K L : SSet.{u}) : ⨆ s, smallProductPiece K L s = ⊤ := by
  simpa only [smallProductPiece, iSup_prod] using iSup_subcomplexOfSimplex_prod_eq_top K L

/-- 正則 κ に対して、元の κ-small な二形状の直積も κ-small。 -/
lemma isKappaSmall_prod {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (K ⊗ L) := by
  have hI : Cardinal.mk (K.N × L.N) < κ := by
    simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
      Cardinal.mul_lt_of_lt hκ.aleph0_le hK hL
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isKappaSmall_of_cover hκ hI (smallProductPiece K L)
    (fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ.aleph0_le _) (iSup_smallProductPiece K L)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
