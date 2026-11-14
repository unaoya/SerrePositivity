module

public import SerrePositivity.EInfinity.SimplexCuts.MixedCornerTerms
public import SerrePositivity.EInfinity.SimplexCuts.UniversalBoundaryValues

/-!
# BF全境界値の混合角の分岐

Berger–Fresse §2.2.7、M14 L09a。
元の実際の境界項の相殺を、構成済みの全添字の対合の混合角の分岐へ戻す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C168：全境界値の出力分岐は、同じ色と面番号の境界項の次数移送。 -/
lemma universalBoundaryValue_output (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (s : Cut (r + d) q) (k : Fin (r + d + q + 1))
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    universalBoundaryValue A S w q x (.inl ⟨s, k⟩) =
      (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (r + 1)).X t) h)).hom
        (outputBoundaryTerm A S s (positiveWord w) (label s (positiveWord w).val k)
          ((colorPositionEquiv s (positiveWord w)).symm k).2 x) := rfl

/-- C169：L09aの混合角の分岐は、元の全境界値で仮定なく相殺する。 -/
lemma universalBoundaryValue_mixed_neg (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌)
    (t : BoundaryVertexOfKind (r + d) q .mixed) :
    universalBoundaryValue A S w q x (.inl (vertexCornerPerm (r + d) q t.val)) =
      -universalBoundaryValue A S w q x (.inl t.val) := by
  rcases t with ⟨⟨s, k⟩, hk⟩
  obtain ⟨h, hc⟩ := (boundaryVertexKind_eq_mixed_iff s k).mp hk
  let a := cornerLeftEdge k h
  let b := cornerRightEdge k h
  have hab : b.val = a.val + 1 := by
    dsimp [a, b, cornerLeftEdge, cornerRightEdge]
    omega
  have hbk : b.castSucc = k := Fin.ext rfl
  have hswap : swapAtVertex s k = s.swapSteps a b := by
    rw [swapAtVertex, dite_eq_left h]
  have ht := outputBoundaryTerm_swapSteps_mixed A S s (positiveWord w) a b hab hc
    ((colorPositionEquiv s (positiveWord w)).symm b.castSucc).2
    (vertexRank_symm_colorPositionEquiv s (positiveWord w) b.castSucc).symm
    ((colorPositionEquiv (s.swapSteps a b) (positiveWord w)).symm b.castSucc).2
    (vertexRank_symm_colorPositionEquiv (s.swapSteps a b) (positiveWord w) b.castSucc).symm x
  rw [hbk] at ht
  have he : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 =
      -((d + q : ℕ) : ℤ) + 1 := by omega
  rw [vertexCornerPerm_apply]
  change universalBoundaryValue A S w q x (.inl ⟨swapAtVertex s k, k⟩) = _
  rw [hswap, universalBoundaryValue_output A S w q x _ _ he,
    universalBoundaryValue_output A S w q x _ _ he, ht, map_neg]

end SerrePositivity.EInfinity.SimplexCuts
