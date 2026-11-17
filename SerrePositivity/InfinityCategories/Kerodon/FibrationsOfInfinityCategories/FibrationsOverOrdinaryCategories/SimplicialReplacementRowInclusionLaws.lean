module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowParts

/-!
概要：同じ基底射列の余積包含と、指定部分への包含の係数射の法則。
方針：元の行の単体ごとの依存和を評価する。
規約：基底部分集合は任意。元の包含と係数射を厳密な等式で保持する。
使われ方：IS-W2 R03f.2の相対latchingの直接の境界付き持ち上げ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
variable {I : Type u} [SmallCategory I] {F G : I ⥤ SSet.{u}} (n : ℕ)

/-- 元の同じ基底射列の係数を、指定部分に含める。 -/
def simplicialReplacementRowPartInclusion (F : I ⥤ SSet.{u}) (P : Set (ComposableArrows I n))
    (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRowPart F n P :=
  Subcomplex.lift (simplicialReplacementRowInclusion F n σ) (by
    rintro q _ ⟨x,rfl⟩
    exact hσ)

/-- 指定部分の包含は、元の同じ余積包含を回収する。 -/
theorem simplicialReplacementRowPartInclusion_inclusion (F : I ⥤ SSet.{u})
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    simplicialReplacementRowPartInclusion n F P σ hσ ≫ (simplicialReplacementRowPart F n P).ι =
      simplicialReplacementRowInclusion F n σ := rfl

/-- 指定部分の同じ係数の包含は、元の係数射と厳密に可換する。 -/
theorem simplicialReplacementRowPartInclusion_map (η : F ⟶ G)
    (P : Set (ComposableArrows I n)) (σ : ComposableArrows I n) (hσ : σ ∈ P) :
    η.app (σ.obj 0) ≫ simplicialReplacementRowPartInclusion n G P σ hσ =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ simplicialReplacementRowPartMap η n P := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 各余積成分の同じ係数射は、元の行の係数射と可換する。 -/
theorem simplicialReplacementRowInclusion_map (η : F ⟶ G) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowMap η n =
      η.app (σ.obj 0) ≫ simplicialReplacementRowInclusion G n σ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 行の二つの射は、元の全基底射列での値で決まる。 -/
theorem simplicialReplacementRow_hom_ext {E : SSet.{u}}
    (f g : simplicialReplacementRow F n ⟶ E)
    (h : ∀ σ, simplicialReplacementRowInclusion F n σ ≫ f =
      simplicialReplacementRowInclusion F n σ ≫ g) : f = g := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨σ,x⟩
  exact ConcreteCategory.congr_hom (congr_app (h σ) q) x

/-- 元の余積からの降下は、各指定包含の射を厳密に回収する。 -/
theorem simplicialReplacementRowDesc_inclusion
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) (σ : ComposableArrows I n) :
    simplicialReplacementRowInclusion F n σ ≫ simplicialReplacementRowDesc F n s = s.inj σ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 指定部分の二つの射は、その同じ全係数上の値で決まる。 -/
theorem simplicialReplacementRowPart_hom_ext (P : Set (ComposableArrows I n)) {E : SSet.{u}}
    (f g : (simplicialReplacementRowPart F n P : SSet.{u}) ⟶ E)
    (h : ∀ σ hσ, simplicialReplacementRowPartInclusion n F P σ hσ ≫ f =
      simplicialReplacementRowPartInclusion n F P σ hσ ≫ g) : f = g := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ,x⟩,hσ⟩
  exact ConcreteCategory.congr_hom (congr_app (h σ hσ) q) x

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
