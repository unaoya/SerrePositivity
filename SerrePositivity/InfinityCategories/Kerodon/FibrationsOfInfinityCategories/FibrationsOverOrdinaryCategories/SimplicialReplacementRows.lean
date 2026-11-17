module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：barの各基底射列における係数を、同じ射列で添字づけた余積として表示する。
方針：単体ごとの依存和で行を構成し、同じ余積包含からの降下を直接与える。
規約：全添字と係数は同じ宇宙。各行の係数の次数を基底射列の次数から独立に保つ。
使われ方：IS-W2 R03f.2のbarの退化部分と相対latchingの分離。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) (n : ℕ)

/-- 同じ基底射列で添字づけた、元の係数の単体集合の行。 -/
def simplicialReplacementRow : SSet.{u} where
  obj m := Σ σ : ComposableArrows I n, (F.obj (σ.obj 0)).obj m
  map θ := ↾fun s => ⟨s.1, (F.obj (s.1.obj 0)).map θ s.2⟩
  map_id m := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    exact congrArg (Sigma.mk σ) (ConcreteCategory.congr_hom ((F.obj (σ.obj 0)).map_id m) x)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    exact congrArg (Sigma.mk σ)
      (ConcreteCategory.congr_hom ((F.obj (σ.obj 0)).map_comp θ φ) x)

/-- 元の同じ基底射列の係数の、行への余積包含。 -/
def simplicialReplacementRowInclusion (σ : ComposableArrows I n) :
    F.obj (σ.obj 0) ⟶ simplicialReplacementRow F n where
  app _ := ↾fun x => (⟨σ,x⟩ : Σ τ : ComposableArrows I n, (F.obj (τ.obj 0)).obj _)
  naturality _ _ _ := rfl

/-- 指定された同じ包含を持つ行の余錐。 -/
def simplicialReplacementRowCofan : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0)) :=
  Cofan.mk (simplicialReplacementRow F n) (simplicialReplacementRowInclusion F n)

/-- 各係数の指定された射から、同じ行へ厳密に降下する。 -/
def simplicialReplacementRowDesc
    (s : Cofan (fun σ : ComposableArrows I n => F.obj (σ.obj 0))) :
    simplicialReplacementRow F n ⟶ s.pt where
  app m := ↾fun x => (s.inj x.1).app m x.2
  naturality m m' θ := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    exact ConcreteCategory.congr_hom ((s.inj σ).naturality θ) x

/-- 同じ係数の包含を持つ元の行は、係数の実際の余積である。 -/
def simplicialReplacementRowIsColimit : IsColimit (simplicialReplacementRowCofan F n) := by
  refine Cofan.IsColimit.mk _ (simplicialReplacementRowDesc F n) ?_ ?_
  · intro s σ
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  · intro s k hk
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    rintro ⟨σ,x⟩
    have h := ConcreteCategory.congr_hom (congr_app (hk σ) m) x
    change k.app m ⟨σ,x⟩ = (s.inj σ).app m x at h
    exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
