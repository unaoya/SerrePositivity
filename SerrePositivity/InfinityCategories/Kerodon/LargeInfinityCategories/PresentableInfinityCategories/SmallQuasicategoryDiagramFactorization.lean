module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallHullCardinal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeRestriction

/-!
概要：小さい試験図式を同じ濃度の quasicategory を通して厳密に因子化する。
方針：図式の像の次数別濃度を評価し、公開された有界 Hull を使う。
規約：新たな充填選択や閉包の複製を行わない。
使われ方：引き戻しの compact comma の余錐を全試験形状へ拡張する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：μ-small な全図式は μ-small な quasicategory を厳密に経由する。
方針：元の像部分複体の有界 Hull に、同じ全図式を因子化する。
規約：始形状に quasicategory 性を要求せず、元の全射の等式を保持する。
使われ方：全 μ-small 試験形状に対する余錐の構成。 -/
lemma exists_kappaSmallQuasicategory_factorization {μ : Cardinal.{u}}
    [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (K : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) :
    ∃ (L : SSet.{u}) (hL : Quasicategory L),
      letI := hL
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ L ∧ ∃ (a : K ⟶ L)
        (j : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ C),
        (SSet.uliftFunctor.{u + 1, u}).map a ≫ j = r := by
  have hreg := (inferInstance : Fact μ.IsRegular).out
  have hKN : HasCardinalLT K.N μ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  let A := SSet.Subcomplex.range r
  have hA : HasCardinalLT A.toSSet.N μ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_N_of_obj hreg hμ
    intro n
    have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N hreg K hKN n
    have hu : HasCardinalLT (((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋n⦌) μ := by
      change HasCardinalLT (ULift.{u + 1} (K _⦋n⦌)) μ
      simpa only [hasCardinalLT_ulift_iff] using hn
    change HasCardinalLT (Set.range (fun s ↦ r.app (Opposite.op ⦋n⦌) s)) μ
    apply hu.of_surjective (fun s ↦
      (⟨r.app (Opposite.op ⦋n⦌) s, Set.mem_range_self s⟩ :
        Set.range (fun t ↦ r.app (Opposite.op ⦋n⦌) t)))
    rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hullOfCardinalBound.{u, u + 1} hreg A hA
  obtain ⟨a, ha⟩ := H.factor r le_rfl
  refine ⟨H.obj, H.quasicategory, ?_, a, H.inclusion, ha⟩
  exact (hasCardinalLT_iff_cardinal_mk_lt _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_hullOfCardinalBound_obj.{u, u + 1} hreg hμ A hA)

/-- 概要：quasicategory である試験形状の余錐から全 μ-small 形状の余錐が従う。
方針：有界な充填模型に因子化し、その余錐を元の図式へ制限する。
規約：元の図式を等式で保ち、頂点族への縮約を使わない。
使われ方：小さい生成添字の κ-filtered 性の試験。 -/
lemma nonempty_cocone_of_smallQuasicategory_tests {μ : Cardinal.{u}}
    [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    (hC : ∀ (L : SSet.{u}) [Quasicategory L], _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ L →
      ∀ j : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ C, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone j))
    (K : SSet.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) := by
  obtain ⟨L, hL, hsmall, a, j, ha⟩ := exists_kappaSmallQuasicategory_factorization hμ K hK r
  have := hL
  obtain ⟨c⟩ := hC L hsmall j
  have hc : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ j)) :=
    ⟨c.restrict ((SSet.uliftFunctor.{u + 1, u}).map a)⟩
  exact ha ▸ hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
