module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ProductComparisonUnitReflection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TotalKanProductFiniteLifting

/-!
概要：filtered な底上の積比較は、有限写像空間の連結成分で単射。
方針：任意の有限射を元の引き戻しへの射で表示し、二射影の同時ホモトピー検出を使う。
規約：元の積比較そのものを検査する。
使われ方：一般 coherent filtered 余極限の有限積比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：積比較は有限形状からの写像空間の連結成分で単射。
方針：引き戻しも底上の left fibration なので元の有限射へ戻し、両成分を同時検出する。
規約：一般の filtered な底と元の二射影。使われ方：有限積比較の検査の単射側。 -/
lemma totalKanProductComparison_mapPiZero_injective {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    Function.Injective (SSet.mapπ₀ ((ihom K).map (totalKanProductComparison p q))) := by
  have : LeftFibration (pullback.fst p q) :=
    ⟨leftFibrations.pullback_fst p q (LeftFibration.mem (p := q))⟩
  let z := pullback.fst p q ≫ p
  have : LeftFibration z := ⟨leftFibrations.comp_mem _ _
    (LeftFibration.mem (p := pullback.fst p q)) (LeftFibration.mem (p := p))⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective x
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective y
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K _).surjective x
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K _).surjective y
  obtain ⟨b, s, ⟨Hs⟩⟩ := continuousKanLeftFibration_finite_fiber_detection_unreplaced z f
  obtain ⟨c, t, ⟨Ht⟩⟩ := continuousKanLeftFibration_finite_fiber_detection_unreplaced z g
  let a := s ≫ vertexFiberι z b
  let a' := t ≫ vertexFiberι z c
  have hs : SSet.π₀.mk (functorVertex f) =
      SSet.π₀.mk (functorVertex (a ≫ continuousKanReplacementUnit.app (pullback p q))) :=
    (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨Hs⟩
  have ht : SSet.π₀.mk (functorVertex g) =
      SSet.π₀.mk (functorVertex (a' ≫ continuousKanReplacementUnit.app (pullback p q))) :=
    (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨Ht⟩
  let m := SSet.mapπ₀ ((ihom K).map (totalKanProductComparison p q))
  have hc := (congrArg m hs).symm.trans (hxy.trans (congrArg m ht))
  have he : continuousKanReplacementUnit.app (pullback p q) ≫
      totalKanProductComparison p q ≫
        fst (continuousKanReplacement.obj E) (continuousKanReplacement.obj D) =
      pullback.fst p q ≫ continuousKanReplacementUnit.app E := by
    rw [← Category.assoc, totalKanProductComparison_unit, lift_fst]
  have hd : continuousKanReplacementUnit.app (pullback p q) ≫
      totalKanProductComparison p q ≫
        snd (continuousKanReplacement.obj E) (continuousKanReplacement.obj D) =
      pullback.snd p q ≫ continuousKanReplacementUnit.app D := by
    rw [← Category.assoc, totalKanProductComparison_unit, lift_snd]
  have h₀ := congrArg (SSet.mapπ₀ ((ihom K).map
    (fst (continuousKanReplacement.obj E) (continuousKanReplacement.obj D)))) hc
  have h₁ := congrArg (SSet.mapπ₀ ((ihom K).map
    (snd (continuousKanReplacement.obj E) (continuousKanReplacement.obj D)))) hc
  change SSet.π₀.mk (functorVertex (((a ≫ continuousKanReplacementUnit.app (pullback p q)) ≫
    totalKanProductComparison p q) ≫
      fst (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))) =
    SSet.π₀.mk (functorVertex (((a' ≫ continuousKanReplacementUnit.app (pullback p q)) ≫
      totalKanProductComparison p q) ≫
        fst (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))) at h₀
  change SSet.π₀.mk (functorVertex (((a ≫ continuousKanReplacementUnit.app (pullback p q)) ≫
    totalKanProductComparison p q) ≫
      snd (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))) =
    SSet.π₀.mk (functorVertex (((a' ≫ continuousKanReplacementUnit.app (pullback p q)) ≫
      totalKanProductComparison p q) ≫
        snd (continuousKanReplacement.obj E) (continuousKanReplacement.obj D))) at h₁
  simp only [Category.assoc, he] at h₀
  simp only [Category.assoc, hd] at h₁
  exact hs.trans ((totalKanProductComparison_unit_reflects_components p q a a' h₀ h₁).trans ht.symm)

/-- 概要：有限写像空間の連結成分で積比較は全単射。
方針：同時有限検出の全射側と共通境界を保つ単射側を合わせる。
規約：全有限形状。使われ方：積比較の有限試験対象による検査。 -/
lemma totalKanProductComparison_mapPiZero_bijective {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    Function.Bijective (SSet.mapπ₀ ((ihom K).map (totalKanProductComparison p q))) :=
  ⟨totalKanProductComparison_mapPiZero_injective p q,
    totalKanProductComparison_mapPiZero_surjective p q⟩

end SerrePositivity.InfinityCategories.F2
