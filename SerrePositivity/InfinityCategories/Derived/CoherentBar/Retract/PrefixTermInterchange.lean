module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixBlockInterchange
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixDegeneracyComposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateFaceCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanDescent
/-!
概要：重複頂点より前の prefix について、退化との前後の合成は同じ全 Hom 要素である。
方針：両側の係数を一つのシフトブロックに戻し、厳密な tail ラベル比較で直和包含を同定する。
規約：始域・終域と切断の全パラメーターを保持する。
使われ方：正規化境界の prefix 和を項ごとに相殺する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

set_option maxHeartbeats 2400000 in
-- 二つの中間対象と終点の直和包含を全 Hom で同時に照合する局所上限。
lemma dgCoherentBarPrefixColumn_degeneracy_interchange {n : ℕ} (s : I _⦋n⦌)
    (k q : ℕ) (hk : k + 1 ≤ n - q) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s ⟨n - q, by omega⟩)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarPrefixColumn R D F (I.σ ⟨n - q, by omega⟩ s) k (by omega))
      (dgCoherentBarDegeneracyBlock R D F s ⟨n - q, by omega⟩)
      (show (-1 : ℤ) + 1 = 0 from rfl) =
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s (k + 1) (by omega))))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarDegeneracyColumn R D F (dgCoherentBarTail s (k + 1) (by omega)).2
        ⟨n - (k + 1) - q, by change n - (k + 1) - q < n - (k + 1) + 1; omega⟩)
      (dgCoherentBarPrefixBlock R D F s k (by omega))
      (show (1 : ℤ) + -1 = 0 from rfl) := by
  have hc := dgCoherentBarPrefixBlock_degeneracy_interchange_heq R D F s k q hk
  let j : Fin (n + 1) := ⟨n - q, by omega⟩
  let t : dgCoherentBarIndex I :=
    ⟨n - (k + 1), (dgCoherentBarTail s (k + 1) (by omega)).2⟩
  let l : dgCoherentBarIndex I :=
    ⟨n + 1 - (k + 1), (dgCoherentBarTail (I.σ j s) (k + 1) (by omega)).2⟩
  let r := dgCoherentBarDegeneracyAt q t
  let a := dgCoherentBarDegeneracyBlock R D F s j
  let b := dgCoherentBarPrefixBlock R D F (I.σ j s) k (by omega)
  let c := dgCoherentBarPrefixBlock R D F s k (by omega)
  let d := dgCoherentBarDegeneracyBlock R D F t.2
    (⟨n - (k + 1) - q, by change n - (k + 1) - q < n - (k + 1) + 1; omega⟩)
  have hleft := dgCoherentBarHom_postcompose_comp R D
    (M := dgCoherentBarFamily R D F ⟨n, s⟩)
    (N := dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j))
    (P := dgCoherentBarFamily R D F l) (Q := dgCoherentBarGraded R D F)
    (Sigma.ι (dgCoherentBarFamily R D F) l) a b (show (-1 : ℤ) + 1 = 0 from rfl)
  have hright := dgCoherentBarHom_postcompose_comp R D
    (M := dgCoherentBarFamily R D F ⟨n, s⟩)
    (N := dgCoherentBarFamily R D F t) (P := dgCoherentBarFamily R D F r)
    (Q := dgCoherentBarGraded R D F)
    (Sigma.ι (dgCoherentBarFamily R D F) r) c d (show (1 : ℤ) + -1 = 0 from rfl)
  have hinc := dgCoherentBarPostInclusion_eq_of_heq R D F ⟨n, s⟩ l r
    (dgCoherentBarTail_degeneracy_at s q (k + 1) hk) 0
    (compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j)))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F l)) b a rfl)
    (compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F t))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F r)) d c rfl) hc
  have hcolLeft :
      (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j))
        (Sigma.ι (dgCoherentBarFamily R D F) l)).f 1 b =
        dgCoherentBarPrefixColumn R D F (I.σ j s) k (by omega) := by
    rfl
  have hcolRight :
      (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F t)
        (Sigma.ι (dgCoherentBarFamily R D F) r)).f (-1) d =
        dgCoherentBarDegeneracyColumn R D F t.2
          ⟨n - (k + 1) - q, by change n - (k + 1) - q < n - (k + 1) + 1; omega⟩ := by
    exact dgCoherentBarDegeneracyAt_column R D F t q
  have hleft' := congrArg (fun w => compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s j)))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) w a
    (show (-1 : ℤ) + 1 = 0 from rfl)) hcolLeft
  have hright' := congrArg (fun w => compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F t))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) w c
    (show (1 : ℤ) + -1 = 0 from rfl)) hcolRight
  exact (hleft.trans hleft').symm.trans (hinc.trans (hright.trans hright'))

end SerrePositivity.InfinityCategories
