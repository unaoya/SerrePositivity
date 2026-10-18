module

public import SerrePositivity.InfinityCategories.F1B.MappingArrowAdjunction
public import SerrePositivity.InfinityCategories.F1B.FunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.F1B.FunctorCompositionRestriction

/-!
概要：指定した自然な単位候補から coherent な矢印比較を構成する。
方針：矢印空間全体で単位と G による後合成を合成し、comma へ持ち上げる。
規約：各点で別々の合成を選ばず、全パラメータを保持する一つの合成を選ぶ。
使われ方：B1 の随伴から coherent な写像空間対応への順方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
namespace MappingArrowComparison
variable {X Y : SSet.{u}} [Quasicategory X] {F : X ⟶ Y} {G : Y ⟶ X}
variable (η : FunctorHom (𝟙 X) (F ≫ G))

/-- 概要：全矢印空間の始域で指定単位を制限した前辺。
方針：単位代表の raw な前合成と端点の正規化。
規約：非定値の全始域を保持する。使われ方：coherent な比較の普遍合成。 -/
def ofUnitLeft : SSet.Homotopy (leftMappingArrowSource F)
    ((leftMappingArrowSource F ≫ F) ≫ G) where
  h := (leftMappingArrowSource F ▷ (Δ[1] : SSet.{u})) ≫ (functorHomHomotopy η).h
  h₀ := by rw [SSet.ι₀_comp_assoc, (functorHomHomotopy η).h₀]; rfl
  h₁ := by rw [SSet.ι₁_comp_assoc, (functorHomHomotopy η).h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：普遍矢印に G を適用した後辺。
方針：矢印空間の普遍ホモトピーを後合成する。
規約：全矢印の族を同時に扱う。使われ方：coherent な比較の普遍合成。 -/
def ofUnitRight : SSet.Homotopy ((leftMappingArrowSource F ≫ F) ≫ G)
    (leftMappingArrowTarget F ≫ G) where
  h := (leftMappingArrowHomotopy (𝟙 (leftMappingArrow F))).h ≫ G
  h₀ := by rw [← Category.assoc, (leftMappingArrowHomotopy (𝟙 (leftMappingArrow F))).h₀]; rfl
  h₁ := by rw [← Category.assoc, (leftMappingArrowHomotopy (𝟙 (leftMappingArrow F))).h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：指定単位候補から得た coherent な矢印比較。
方針：普遍前辺と普遍後辺を一つのホモトピーに合成し、comma へ持ち上げる。
規約：単位に普遍性・同値性を仮定しない。
使われ方：随伴が誘導する自然な対応の全パラメータ表示。 -/
def ofUnitHom : MappingArrowComparison F G where
  map := unitCommaLift G (leftMappingArrowSource F) (leftMappingArrowTarget F)
    (functorHomotopyComposite (ofUnitLeft η) (ofUnitRight (F := F) (G := G)))
  source := unitCommaLift_source _ _ _ _
  target := unitCommaLift_target _ _ _ _

/-- 概要：構成した比較の恒等矢印の像は元の指定単位候補を回収する。
方針：普遍合成三角形を恒等矢印の族へ制限し、後辺を恒等に認識する。
規約：各点の等式から全体の等式を推論せず、h Fun 全体の等式を得る。
使われ方：元の随伴の単位と各点の標準比較への接続。 -/
lemma ofUnitHom_unitHom : (ofUnitHom η).unitHom = η := by
  let l := ofUnitLeft η
  let r := ofUnitRight (F := F) (G := G)
  let T := functorHomotopyCompositeTriangle l r
  have hl : (functorHomHomotopy η).h =
      (leftMappingArrowIdentityFamily F ▷ (Δ[1] : SSet.{u})) ≫ l.h := by
    change _ = (_ ▷ (Δ[1] : SSet.{u})) ≫
      (leftMappingArrowSource F ▷ (Δ[1] : SSet.{u})) ≫ (functorHomHomotopy η).h
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      leftMappingArrowIdentityFamily_source, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have hr : (functorHomotopyRefl (F ≫ G)).h =
      (leftMappingArrowIdentityFamily F ▷ (Δ[1] : SSet.{u})) ≫ r.h := by
    change _ = (_ ▷ (Δ[1] : SSet.{u})) ≫
      (leftMappingArrowHomotopy (𝟙 (leftMappingArrow F))).h ≫ G
    have h := leftMappingArrowHomotopy_precomp_h (leftMappingArrowIdentityFamily F)
      (𝟙 (leftMappingArrow F))
    have hi : (leftMappingArrowHomotopy (leftMappingArrowIdentityFamily F)).h =
        (leftMappingArrowIdentityFamily F ▷ (Δ[1] : SSet.{u})) ≫
          (leftMappingArrowHomotopy (𝟙 (leftMappingArrow F))).h := h
    rw [← Category.assoc, ← hi, leftMappingArrowIdentityFamily_h, Category.assoc]
    rfl
  have hd : (ofUnitHom η).unitHomotopy.h =
      (leftMappingArrowIdentityFamily F ▷ (Δ[1] : SSet.{u})) ≫
        (functorHomotopyComposite l r).h := by
    change (unitCommaHomotopy (leftMappingArrowIdentityFamily F ≫
      unitCommaLift G _ _ (functorHomotopyComposite l r))).h = _
    rw [unitCommaHomotopy_precomp, unitCommaHomotopy_lift_h]
  let T' := T.precompOfRaw (leftMappingArrowIdentityFamily F)
    (functorHomHomotopy η) (functorHomotopyRefl (F ≫ G))
    (ofUnitHom η).unitHomotopy hl hr hd
  have h := T'.hom_eq
  rw [functorHomHomotopy_hom, functorHomotopyRefl_hom] at h
  exact (Category.comp_id η).symm.trans h |>.symm

end MappingArrowComparison
end SerrePositivity.InfinityCategories
