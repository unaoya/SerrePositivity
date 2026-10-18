module

public import SerrePositivity.InfinityCategories.F1B.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Core.RelativeEquivalencePath

/-!
概要：同じ始点と基底 path を持つ二つの可逆 path の終点を基底上で比較する。
方針：相対 path 写像の同じ射の二つの持ち上げを、その fiber 内で結ぶ。
規約：終点のホモトピーも元の基底への射を全時間で固定する。
使われ方：B1 の元の正方形と指定境界輸送で復元した正方形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始点と基底 path が一致する二つの輸送の終点は基底上でホモトピック。
方針：相対 path 写像を通じて比較し、同じ fiber 内のホモトピーを終点で評価する。
規約：比較する path の終点だけの一致は仮定せず、path の像全体を固定する。
使われ方：境界を保持した輸送の一意性。 -/
lemma exists_relativePathEndpointHomotopy {C E B : SSet.{u}} (p : E ⟶ B)
    [TrivialKanFibration (relativeEquivalencePathMap p)]
    (a b : C ⟶ equivalencePath E)
    (hpath : a ≫ equivalencePathMap p = b ≫ equivalencePathMap p)
    (hstart : a ≫ equivalencePathEndpoint E 0 = b ≫ equivalencePathEndpoint E 0) :
    ∃ H : SSet.Homotopy (a ≫ equivalencePathEndpoint E 1) (b ≫ equivalencePathEndpoint E 1),
      H.h ≫ p = fst C (Δ[1] : SSet.{u}) ≫ b ≫ equivalencePathEndpoint E 1 ≫ p := by
  let q := relativeEquivalencePathMap p
  have hq : a ≫ q = b ≫ q := by
    apply pullback.hom_ext
    · simpa only [q, Category.assoc, relativeEquivalencePathMap_fst] using hpath
    · simpa only [q, Category.assoc, relativeEquivalencePathMap_snd] using hstart
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration q a b hq
  let D : SSet.Homotopy (a ≫ equivalencePathEndpoint E 1) (b ≫ equivalencePathEndpoint E 1) :=
    { h := H.h ≫ equivalencePathEndpoint E 1
      h₀ := by rw [← Category.assoc, H.h₀]; rfl
      h₁ := by rw [← Category.assoc, H.h₁]; rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        exact False.elim s.1.property }
  refine ⟨D, ?_⟩
  have he : q ≫ pullback.fst (equivalencePathEndpoint B 0) p ≫ equivalencePathEndpoint B 1 =
      equivalencePathEndpoint E 1 ≫ p := by
    rw [← Category.assoc, relativeEquivalencePathMap_fst, equivalencePathMap_endpoint]
  have hc := congrArg
    (fun k ↦ k ≫ pullback.fst (equivalencePathEndpoint B 0) p ≫ equivalencePathEndpoint B 1) hH
  change (H.h ≫ equivalencePathEndpoint E 1) ≫ p = _
  simpa only [Category.assoc, he] using hc

end SerrePositivity.InfinityCategories
