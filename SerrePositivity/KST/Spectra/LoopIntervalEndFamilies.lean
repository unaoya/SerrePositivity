module

public import SerrePositivity.KST.Spectra.CospanLoopWeights
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections
public import SerrePositivity.KST.Spectra.PathContractibility

/-!
概要：区間重みの end の普遍族は、両端で標的の基点を取る。
方針：二つの構造射に対する end の自然性を uncurry して端点を計算する。
規約：実際の中央射影と元の評価族を使う。使われ方：円の写像空間への商による降下。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

/-- 点を両端とし、両構造射を基点へ送る係数 cospan。 -/
def loopCoefficient (Y : PointedSimplicialSet.{u}) : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  AsSmall.down ⋙ cospan (SSet.const (X := (Δ[0] : SSet.{u})) Y.basepoint)
    (SSet.const (X := (Δ[0] : SSet.{u})) Y.basepoint)

/-- 区間の end の実際の中央射影を uncurry した普遍評価族。 -/
def loopIntervalEndFamily (Y : PointedSimplicialSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) ⟶ Y.right :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y)))).app
    (AsSmall.up.obj .one)

/-- 左端での普遍評価族は、標的の基点で定数。 -/
lemma loopIntervalEndFamily_left (Y : PointedSimplicialSet.{u}) :
    (stdSimplex.δ (1 : Fin 2) ▷ _) ≫ loopIntervalEndFamily Y =
      SSet.const Y.basepoint := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y)))).naturality
      (AsSmall.up.map WalkingCospan.Hom.inl)
  change (stdSimplex.δ (1 : Fin 2) ▷ _) ≫ loopIntervalEndFamily Y =
    _ ≫ SSet.const Y.basepoint at h
  simpa only [SSet.comp_const] using h

/-- 右端での普遍評価族も、標的の基点で定数。 -/
lemma loopIntervalEndFamily_right (Y : PointedSimplicialSet.{u}) :
    (stdSimplex.δ (0 : Fin 2) ▷ _) ≫ loopIntervalEndFamily Y =
      SSet.const Y.basepoint := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y)))).naturality
      (AsSmall.up.map WalkingCospan.Hom.inr)
  change (stdSimplex.δ (0 : Fin 2) ▷ _) ≫ loopIntervalEndFamily Y =
    _ ≫ SSet.const Y.basepoint at h
  simpa only [SSet.comp_const] using h

/-- 両端で基点を取る区間上の族は、区間 end へ持ち上がる。 -/
def loopIntervalEndLift (Y : PointedSimplicialSet.{u}) {P : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⊗ P ⟶ Y.right)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ P) ≫ a = SSet.const Y.basepoint)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ P) ≫ a = SSet.const Y.basepoint) :
    P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift {
    app i := match i with
      | ⟨none⟩ => a
      | ⟨some .left⟩ => stdSimplex.isTerminalObj₀.from _
      | ⟨some .right⟩ => stdSimplex.isTerminalObj₀.from _
    naturality := by
      rintro ⟨i⟩ ⟨j⟩ ⟨f⟩
      change WidePullbackShape.Hom i j at f
      cases f with
      | id i =>
        change ((loopIntervalWeight ⊗ (Functor.const _).obj P).map
          (𝟙 (AsSmall.up.obj i))) ≫ _ = _ ≫ (loopCoefficient Y).map (𝟙 _)
        simp
      | term k =>
        cases k
        · change (stdSimplex.δ (1 : Fin 2) ▷ P) ≫ a = _ ≫ SSet.const Y.basepoint
          rw [h₀, SSet.comp_const]
        · change (stdSimplex.δ (0 : Fin 2) ▷ P) ≫ a = _ ≫ SSet.const Y.basepoint
          rw [h₁, SSet.comp_const] }

/-- 持ち上げの中央射影は、指定した元の区間上の族の curry。 -/
lemma loopIntervalEndLift_central (Y : PointedSimplicialSet.{u}) {P : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⊗ P ⟶ Y.right) (h₀ h₁) :
    loopIntervalEndLift Y a h₀ h₁ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one) =
      curry a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π _ _

/-- 両端の係数が一点なので、区間 end への射は中央射影で決まる。 -/
lemma loopIntervalEnd_hom_ext (Y : PointedSimplicialSet.{u}) {P : SSet.{u}}
    {a b : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections loopIntervalWeight (loopCoefficient Y)}
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one) =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ loopIntervalWeight (loopCoefficient Y) (AsSmall.up.obj .one)) :
    a = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  rintro ⟨i⟩
  cases i with
  | none => exact h
  | some i =>
    cases i <;> apply uncurry_injective <;> exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.Spectra
