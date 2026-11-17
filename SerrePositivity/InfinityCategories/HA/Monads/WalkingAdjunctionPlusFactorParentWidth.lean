module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicFactorWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionWidthOneGenerator
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentWidth

/-!
概要：生成射を前置した単独の原子でない実鎖では、始点plusの任意の原子因子の実親も幅が小さい。
方針：前後の実幅の和が1以下の場合を、幅1の実生成射と空の実後続道へ戻して排除する。
規約：実道の指定因子と構成済みの実親を結論に保持する。
使われ方：Riehl–Verity Proposition 4.2.15の境界因子の実親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の幅が1増える実親の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実生成射の前置でないminus始点の鎖では、始点plusの任意の実原子因子の実親の幅が小さい。
方針：先行道の実幅は正であり、前後の幅の和が1なら、後続道は空、先行道は実生成射となる。
規約：実親の幅の正値を新しい仮定にしない。使われ方：Riehl–Verity §4.2の境界の実親。 -/
lemma walkingAdjunctionPlusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (F : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = F)
    (hno : ∀ E : ComposableArrows (walkingAdjunctionHom .plus Y) n,
      WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E →
        F ≠ walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth F := by
  have hqpos :
      0 < walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) := by
    by_contra hn
    have hz : walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) = 0 :=
      by omega
    have hs := (walkingAdjunctionOrdinalWidth_zero_iff_size_zero _).mp hz
    have he := walkingAdjunctionLevelSize_zero_endpoints
      ((walkingAdjunctionAtomicPathFunctor n).map q) hs
    cases he
  have hsum : 2 ≤
      walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) +
      walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map r) := by
    by_contra hn
    have hqone : walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map q) = 1 :=
      by omega
    have hrzero :
        walkingAdjunctionOrdinalWidth ((walkingAdjunctionAtomicPathFunctor n).map r) = 0 :=
      by omega
    have hrs := (walkingAdjunctionOrdinalWidth_zero_iff_size_zero _).mp hrzero
    have hrlen : r.length = 0 := by
      by_contra hr
      have hp := walkingAdjunctionAtomicPathFunctor_size_pos r (Nat.pos_of_ne_zero hr)
      omega
    have hC := r.eq_of_length_zero hrlen
    subst C
    have hrnil := r.eq_nil_of_length_zero hrlen
    subst r
    have hqeq := walkingAdjunctionWidthOne_minus_plus_generator
      ((walkingAdjunctionAtomicPathFunctor n).map q) hqone
    have he : F = ((walkingAdjunctionAtomicPathFunctor n).map q).prod' e.val ⋙
        walkingAdjunctionHorizontal .minus .plus Y := hfac.symm
    apply hno e.val e.property
    simpa only [hqeq, walkingAdjunctionPlusParentPrefix] using he
  have hw := walkingAdjunctionAtomicFactor_width_sum q e r
  rw [hfac] at hw
  have hp := walkingAdjunctionPlusParent_ordinalWidth e.val e.property
  omega

end SerrePositivity.InfinityCategories.HA.Monads
