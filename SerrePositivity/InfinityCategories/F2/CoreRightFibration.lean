module

public import SerrePositivity.InfinityCategories.F2.CoreInvertibleEdgeLifting

/-!
概要：inner fibration と可逆辺の持ち上げから core の右ファイブレーションを構成する。
方針：一次は終点指定の lift、高次は内ホーンと相対外側ホーンで埋めて core に戻す。
規約：右ホーンの全次数で指定された底の単体と境界を保持する。
使われ方：path 置換の core の Kan fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：inner fibration で終点指定の可逆辺を持ち上げる射の core は右ファイブレーション。
方針：低次の辺の持ち上げと高次の相対ホーン充填を組み合わせる。
規約：高次の充填は全ての辺の可逆性を保つことを core のホーン判定で確認する。
使われ方：core の全ホーンの持ち上げ性の構成。 -/
lemma coreMap_rightFibration_of_invertibleTargetLifting
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [InnerFibration p]
    (hp : F1B.KanInvertibleTargetLifting p) : RightFibration (quasicategoryCoreMap p) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hi =>
      constructor
      intro a b sq
      cases n with
      | zero =>
        have hi1 : i = 1 := by fin_cases i <;> first | rfl | exact (lt_irrefl _ hi).elim
        subst i
        obtain ⟨l, hl, hlp⟩ := coreMap_liftHorn_one_last p hp a b sq
        exact CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := hlp }
      | succ n =>
        let a' := a ≫ (quasicategoryCore X).ι
        let b' := b ≫ (quasicategoryCore Y).ι
        have hsq : a' ≫ p = (horn (n + 2) i).ι ≫ b' := by
          dsimp only [a', b']
          rw [Category.assoc, ← quasicategoryCoreMap_ι, ← Category.assoc, sq.w, Category.assoc]
        have hfill : ∃ f : (Δ[n + 2] : SSet.{u}) ⟶ X,
            (horn (n + 2) i).ι ≫ f = a' ∧ f ≫ p = b' := by
          by_cases hilast : i = Fin.last (n + 2)
          · subst i
            exact innerFibration_lift_finalHorn p n a' b' hsq
              (quasicategoryCore_edge (a.app (Opposite.op ⦋1⦌) (finalHornEdge n)))
          · have hi₁ : i < Fin.last (n + 2) := by
              have hval : i.val ≠ n + 2 := fun h ↦ hilast (Fin.ext h)
              change i.val < n + 2
              have := i.isLt
              omega
            have := InnerFibration.mem (q := p) _ (innerHornInclusions.intro i hi hi₁)
            let t : CommSq a' (horn (n + 2) i).ι p b' := ⟨hsq⟩
            exact ⟨t.lift, t.fac_left, t.fac_right⟩
        obtain ⟨f, hfr, hfp⟩ := hfill
        let fc : (Δ[n + 2] : SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}) :=
          SSet.yonedaEquiv.symm ⟨SSet.yonedaEquiv f,
            quasicategoryCore_horn_filler_mem n i a f hfr⟩
        have hfc : fc ≫ (quasicategoryCore X).ι = f := by
          apply SSet.yonedaEquiv.injective
          rw [SSet.yonedaEquiv_comp]
          change (SSet.yonedaEquiv fc).val = _
          rw [Equiv.apply_symm_apply]
        refine CommSq.HasLift.mk' { l := fc, fac_left := ?_, fac_right := ?_ }
        · apply (cancel_mono (quasicategoryCore X).ι).mp
          rw [Category.assoc, hfc]
          exact hfr
        · apply (cancel_mono (quasicategoryCore Y).ι).mp
          rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc, hfc]
          exact hfp

end SerrePositivity.InfinityCategories.F2
