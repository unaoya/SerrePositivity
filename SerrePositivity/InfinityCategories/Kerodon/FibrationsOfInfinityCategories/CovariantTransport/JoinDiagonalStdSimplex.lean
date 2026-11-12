module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoin
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex

/-!
概要：標準単体の区間付き対角の頂点での式と単射性。
方針：通常の join の標準単体表示で、時刻と係数を各頂点の値から回復する。
規約：この単射性の主張は底が標準単体の場合に限る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体上の relative join の部分複体表示。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準単体の対角の像は零時刻では元の頂点、一時刻では右側の頂点になる。
方針：対角円柱を通常の join の円柱比較の頂点の式へ代入する。
規約：右側の頂点番号は n+1 だけずらす。
使われ方：Kerodon Construction 5.2.3.1（Tag 0242）、標準単体上の relative join の頂点条件。 -/
lemma joinDiagonal_stdSimplex_val (n d : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋d⦌) (a : (Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n]).app (Opposite.op ⦋d⦌) (t, a)) i).val =
        if (t i).val = 0 then (a i).val else n + 1 + (a i).val := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val n n d a t a i

/-- 概要：標準単体の区間付き対角は単射。
方針：join の頂点番号の左右の区間から時刻を読み、その残りから係数を読む。
規約：任意の単体集合についての対角の単射性は主張しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体上の relative join の部分複体表示。 -/
instance joinDiagonal_stdSimplex_mono (n : ℕ) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal (Δ[n] : SSet.{u})) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  rintro ⟨t, a⟩ ⟨t', a'⟩ he
  have hv (i : Fin (d + 1)) : t i = t' i ∧ a i = a' i := by
    have hi := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[n] _⦋d⦌ ↦
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n n).hom.app (Opposite.op ⦋d⦌) z i).val) he
    rw [joinDiagonal_stdSimplex_val, joinDiagonal_stdSimplex_val] at hi
    have ht := (t i).isLt
    have ht' := (t' i).isLt
    have ha := (a i).isLt
    have ha' := (a' i).isLt
    constructor <;> apply Fin.ext <;> split_ifs at hi <;> omega
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    exact (hv i).1
  · apply stdSimplex.ext
    intro i
    exact (hv i).2

/-- 概要：標準単体を底とする relative join の通常の join への射影は単射。
方針：標準単体の対角の単射性を pullback で保つ。
規約：両因子と底への射は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、通常の join 内での relative join の同定。 -/
instance relativeJoin_fst_stdSimplex_mono {X Y : SSet.{u}} {n : ℕ}
    (f : X ⟶ (Δ[n] : SSet.{u})) (g : Y ⟶ (Δ[n] : SSet.{u})) :
    Mono (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal Δ[n])) := by
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
