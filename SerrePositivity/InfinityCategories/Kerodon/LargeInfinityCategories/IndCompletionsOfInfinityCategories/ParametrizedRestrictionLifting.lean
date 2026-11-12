module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedSectionRestriction
/-!
概要：相対内部 Hom の全境界持ち上げを、同じパラメータ付き相対切断へ移す。
方針：底の元の族を保った比較対象に持ち上げ、同じパラメータへ戻す。
規約：底の族を定値にしない。使われ方：under 圏の初頂点への制限の同値性。

対応節は Kerodon 9.3（Tag 06FR）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 相対内部 Hom の持ち上げ性は、同じ非定値の底の族の制限へ移る。 -/
lemma parametrizedSectionsPre_trivial_of_relativeHom {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) (sq' : internalHom.PullbackObjObj i p)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration sq'.π] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre p a b i h) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq'.π) (boundary n).ι inferInstance
  constructor
  intro u v sq
  have hbase : u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a =
      (boundary n).ι ≫ v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b := by
    have hh := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) sq.w
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_projection] using hh
  let V : (Δ[n] : SSet.{u}) ⟶ sq'.pt := sq'.isPullback.lift
    (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b) ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) ≫ a) (by
      change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b) ≫ (ihom D).map p =
        ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) ≫ a) ≫ (pre i).app Y
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_condition, Category.assoc, Category.assoc, h])
  have hVfst : V ≫ sq'.fst = v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b := sq'.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ sq'.snd = (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) ≫ a :=
    sq'.isPullback.lift_snd _ _ _
  have ht : CommSq (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a) (boundary n).ι sq'.π V := by
    constructor
    apply sq'.hom_ext
    · simp only [Category.assoc, sq'.π_fst, hVfst]
      change u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a ≫ (pre i).app E =
        (boundary n).ι ≫ v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b
      have hh := congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b) sq.w
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_map] using hh
    · simp only [Category.assoc, sq'.π_snd, hVsnd]
      change (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a) ≫ (ihom A).map p =
        (boundary n).ι ≫ ((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) ≫ a)
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_condition, ← Category.assoc, hbase]
      rfl
  have hproj : ht.lift ≫ (ihom A).map p = (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) ≫ a := by
    calc
      _ = (ht.lift ≫ sq'.π) ≫ sq'.snd := by
        rw [Category.assoc]
        exact congrArg (fun f => ht.lift ≫ f) sq'.π_snd.symm
      _ = V ≫ sq'.snd := congrArg (fun f => f ≫ sq'.snd) ht.fac_right
      _ = _ := hVsnd
  let W := pullback.lift ht.lift (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b) hproj
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_hom_ext p a
    · change (boundary n).ι ≫ W ≫ pullback.fst _ _ = u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a
      rw [pullback.lift_fst]
      exact ht.fac_left
    · change (boundary n).ι ≫ W ≫ pullback.snd _ _ = u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a
      rw [pullback.lift_snd]
      exact hbase.symm
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_hom_ext p b
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_map, ← Category.assoc]
      change (W ≫ pullback.fst _ _) ≫ (pre i).app E = v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b
      rw [pullback.lift_fst]
      calc
        _ = (ht.lift ≫ sq'.π) ≫ sq'.fst := by
          rw [Category.assoc]
          exact congrArg (fun f => ht.lift ≫ f) sq'.π_fst.symm
        _ = V ≫ sq'.fst := congrArg (fun f => f ≫ sq'.fst) ht.fac_right
        _ = _ := hVfst
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_projection]
      exact pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
