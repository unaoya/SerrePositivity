module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornChainNerve
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.NerveChainsLastVertex

/-!
# 二重細分された標準単体から horn への写像

概要：二重細分された標準単体から k-horn への具体的な写像を構成する。
方針：最初の細分の標準同型、順序集合の nerve の細分比較、horn への有限鎖の写像を合成する。
規約：Moss 2020 Proposition 21 の Kan 性に向けた充填候補。境界条件は別の証明項目。
使われ方：Ex∞ の有限段階における horn の充填。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder
open scoped _root_.Simplicial

/--
概要：二重細分された標準単体から k-horn への写像。
方針：sd(Δ[n]) を面の有限鎖の nerve と同定し、二段階の有限鎖からの写像を使う。
規約：正次元を仮定する。horn 上での所要の単位との一致はまだこの定義の主張ではない。
使われ方：Ex の二回の適用で horn の写像を充填する候補。
-/
def doubleSubdivisionHornMap (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    SSet.sd.obj (SSet.sd.obj (Δ[n] : SSet.{u})) ⟶ SSet.horn n k :=
  SSet.sd.map (SSet.stdSimplex.sdIso.hom.app ⦋n⦌) ≫
    subdivisionNerveChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) ≫
      hornChainToHorn n hn k

/--
概要：二重細分から horn への写像を標準単体へ合成した際の具体的な表示。
方針：horn への制限の包含との合成則を使う。
規約：候補の頂点の計算を標準単体の中で行うための規約。
使われ方：horn 上の境界写像との一致の検証。
-/
@[reassoc] theorem doubleSubdivisionHornMap_ι (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    doubleSubdivisionHornMap.{u} n hn k ≫ (SSet.horn n k).ι =
      SSet.sd.map (SSet.stdSimplex.sdIso.hom.app ⦋n⦌) ≫
        subdivisionNerveChains (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) ≫
          hornChainToSimplex n k := by
  simp only [doubleSubdivisionHornMap, Category.assoc, hornChainToHorn,
    SSet.Subcomplex.lift_ι]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
