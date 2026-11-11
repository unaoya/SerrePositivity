module

public import SerrePositivity.KST.LocalizingInvariants.IntervalPostcompositionFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanFamilies

/-!
概要：span の第二終点の指定辺を、第一脚を固定した span の実際の辺へ持ち上げる。
方針：右脚の合成正方形を定値の左脚と共通始点で貼る。
規約：元の span と指定辺を厳密に保持。使われ方：分母付き span の cocartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_spanPostcompositionFamily {X : SSet.{u}} [Quasicategory X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (b : (Δ[1] : SSet.{u}) ⟶ X)
    (hb : stdSimplex.δ (1 : Fin 2) ≫ b =
      stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂ ≫ p) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj X,
      stdSimplex.δ (1 : Fin 2) ≫ F = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ∧
      F ≫ (pre horn₂₀.ι₀₁).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ p)) ∧
      F ≫ (pre horn₂₀.ι₀₂).app X ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = b := by
  obtain ⟨R, hR₀, hRs, hRt⟩ := exists_intervalPostcompositionFamily (horn₂₀.ι₀₂ ≫ p) b
    (by simpa only [Category.assoc] using hb)
  let L : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (horn₂₀.ι₀₁ ≫ p))
  have hLR : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    rw [hRs]
    dsimp only [L]
    rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    rfl
  let F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows L R hLR
  have hFl : F ≫ (pre horn₂₀.ι₀₁).app X = L := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left _ _ _
  have hFr : F ≫ (pre horn₂₀.ι₀₂).app X = R := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right _ _ _
  refine ⟨F, ?_, hFl, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
    · rw [Category.assoc, hFl, SSet.comp_const, SSet.const_comp]
      rfl
    · rw [Category.assoc, hFr, hR₀, SSet.const_comp]
      rfl
  · rw [← Category.assoc, hFr]
    exact hRt

end SerrePositivity.KST.LocalizingInvariants
