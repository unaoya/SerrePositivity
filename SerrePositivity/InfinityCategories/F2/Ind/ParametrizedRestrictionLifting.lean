module
public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedSectionRestriction
/-!
概要：相対内部 Hom の全境界持ち上げを、同じパラメータ付き相対切断へ移す。
方針：底の元の族を保った比較対象に持ち上げ、同じパラメータへ戻す。
規約：底の族を定値にしない。使われ方：under 圏の初頂点への制限の同値性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 相対内部 Hom の持ち上げ性は、同じ非定値の底の族の制限へ移る。 -/
lemma parametrizedSectionsPre_trivial_of_relativeHom {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) (sq' : internalHom.PullbackObjObj i p)
    [TrivialKanFibration sq'.π] : TrivialKanFibration (parametrizedSectionsPre p a b i h) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  have := TrivialKanFibration.mem (p := sq'.π) (boundary n).ι inferInstance
  constructor
  intro u v sq
  have hbase : u ≫ parametrizedSectionsProjection p a =
      (boundary n).ι ≫ v ≫ parametrizedSectionsProjection p b := by
    have hh := congrArg (fun f => f ≫ parametrizedSectionsProjection p b) sq.w
    simpa only [Category.assoc, parametrizedSectionsPre_projection] using hh
  let V : (Δ[n] : SSet.{u}) ⟶ sq'.pt := sq'.isPullback.lift
    (v ≫ parametrizedSectionsMap p b) ((v ≫ parametrizedSectionsProjection p b) ≫ a) (by
      change (v ≫ parametrizedSectionsMap p b) ≫ (ihom D).map p =
        ((v ≫ parametrizedSectionsProjection p b) ≫ a) ≫ (pre i).app Y
      rw [Category.assoc, parametrizedSections_condition, Category.assoc, Category.assoc, h])
  have hVfst : V ≫ sq'.fst = v ≫ parametrizedSectionsMap p b := sq'.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ sq'.snd = (v ≫ parametrizedSectionsProjection p b) ≫ a :=
    sq'.isPullback.lift_snd _ _ _
  have ht : CommSq (u ≫ parametrizedSectionsMap p a) (boundary n).ι sq'.π V := by
    constructor
    apply sq'.hom_ext
    · simp only [Category.assoc, sq'.π_fst, hVfst]
      change u ≫ parametrizedSectionsMap p a ≫ (pre i).app E =
        (boundary n).ι ≫ v ≫ parametrizedSectionsMap p b
      have hh := congrArg (fun f => f ≫ parametrizedSectionsMap p b) sq.w
      simpa only [Category.assoc, parametrizedSectionsPre_map] using hh
    · simp only [Category.assoc, sq'.π_snd, hVsnd]
      change (u ≫ parametrizedSectionsMap p a) ≫ (ihom A).map p =
        (boundary n).ι ≫ ((v ≫ parametrizedSectionsProjection p b) ≫ a)
      rw [Category.assoc, parametrizedSections_condition, ← Category.assoc, hbase]
      rfl
  have hproj : ht.lift ≫ (ihom A).map p = (v ≫ parametrizedSectionsProjection p b) ≫ a := by
    calc
      _ = (ht.lift ≫ sq'.π) ≫ sq'.snd := by
        rw [Category.assoc]
        exact congrArg (fun f => ht.lift ≫ f) sq'.π_snd.symm
      _ = V ≫ sq'.snd := congrArg (fun f => f ≫ sq'.snd) ht.fac_right
      _ = _ := hVsnd
  let W := pullback.lift ht.lift (v ≫ parametrizedSectionsProjection p b) hproj
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply parametrizedSections_hom_ext p a
    · change (boundary n).ι ≫ W ≫ pullback.fst _ _ = u ≫ parametrizedSectionsMap p a
      rw [pullback.lift_fst]
      exact ht.fac_left
    · change (boundary n).ι ≫ W ≫ pullback.snd _ _ = u ≫ parametrizedSectionsProjection p a
      rw [pullback.lift_snd]
      exact hbase.symm
  · apply parametrizedSections_hom_ext p b
    · rw [Category.assoc, parametrizedSectionsPre_map, ← Category.assoc]
      change (W ≫ pullback.fst _ _) ≫ (pre i).app E = v ≫ parametrizedSectionsMap p b
      rw [pullback.lift_fst]
      calc
        _ = (ht.lift ≫ sq'.π) ≫ sq'.fst := by
          rw [Category.assoc]
          exact congrArg (fun f => ht.lift ≫ f) sq'.π_fst.symm
        _ = V ≫ sq'.fst := congrArg (fun f => f ≫ sq'.fst) ht.fac_right
        _ = _ := hVfst
    · rw [Category.assoc, parametrizedSectionsPre_projection]
      exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
