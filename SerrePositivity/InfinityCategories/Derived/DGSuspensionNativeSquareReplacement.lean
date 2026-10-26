module
public import SerrePositivity.InfinityCategories.Derived.NativeDiagramFamilyReplacement
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSquareFamily

/-!
概要：元の選択四角形全体への復帰を、指定部分を固定する相対 path から実構成する。
方針：零骨格上の指定された全比較を同時に延長し、curry を戻す。
規約：元の四角形を四辺だけで同定しない。前提となる作用族と相対 path の存在は別工程。
使われ方：D-8 e の固定懸垂角を保持した、同じ選択二胞体全体の厳密回収。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 同じ選択された全四角形へ厳密に戻し、指定部分の全 native 作用を同時に保つ。 -/
lemma dgSuspensionNativeSquare_exists_replacement
    {A : SSet.{max (u + 1) v + 1}}
    (j : A ⟶ (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1})) [Mono j]
    (F : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
      dgKInputInfinity.{u, max (u + 1) v} R)
    (a : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌ →
      (equivalencePath ((ihom (Δ[1] ⊗ Δ[1])).obj
        (dgKInputInfinity.{u, max (u + 1) v} R))) _⦋0⦌)
    (ha : ∀ k, (equivalencePathMap ((pre j).app _)).app (Opposite.op ⦋0⦌) (a k) =
      ((curry F ≫ (pre j).app _) ≫ equivalencePathRefl _).app (Opposite.op ⦋0⦌) k)
    (hf : ∀ k, (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (a k) =
      (curry F).app (Opposite.op ⦋0⦌) k)
    (hg : ∀ B : PerfDGInput.{u, max (u + 1) v} R,
      (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (a (coherentNerveVertex B)) =
        functorVertex (dgKappaResolvedConnectiveSquare R B (s B).cone)) :
    ∃ G : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
        dgKInputInfinity.{u, max (u + 1) v} R,
      (j ▷ dgKInputInfinity.{u, max (u + 1) v} R) ≫ G =
        (j ▷ dgKInputInfinity.{u, max (u + 1) v} R) ≫ F ∧
      ∀ B : PerfDGInput.{u, max (u + 1) v} R,
        dgSuspensionNativeSquareAt R G B = dgKappaResolvedConnectiveSquare R B (s B).cone := by
  obtain ⟨G, hG, hv⟩ := nativeDiagramFamily_exists_replacement j (curry F) a ha hf
  refine ⟨uncurry G, ?_, ?_⟩
  · have h := congrArg uncurry hG
    simpa only [uncurry_pre_app, uncurry_curry] using h
  · intro B
    have h := (hv (coherentNerveVertex B)).trans (hg B)
    change G.app (Opposite.op ⦋0⦌) (coherentNerveVertex B) = _ at h
    unfold dgSuspensionNativeSquareAt dgSuspensionNativeSquareDiagramFamily
    rw [curry_uncurry, h]
    exact (functorVertexEquiv _ _).symm_apply_apply _

end SerrePositivity.InfinityCategories
