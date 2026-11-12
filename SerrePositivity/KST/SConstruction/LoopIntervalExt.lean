module
public import SerrePositivity.KST.SConstruction.LoopOfCylinder

/-! # 元の区間上の評価による loop 写像族の検出
概要：既存の loop 空間への射は、元の円の区間商射で引き戻した評価で一意に決まる。
方針：点つき内部 Hom の包含と curry の単射性、円の cofiber cylinder の二脚を使う。
規約：Kan 性や局所化を仮定しない。使われ方：元の suspension 随伴と具体的な零行 loop 射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の区間の商射に沿う通常の評価の等号で、既存の loop 空間への写像族を検出する。 -/
lemma loop_interval_hom_ext {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (f g : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
    (h : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
        MonoidalClosed.uncurry (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
      (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
        MonoidalClosed.uncurry (g ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B)) :
    f = g := by
  apply (cancel_mono (PointedObject.basedHomι PointedSimplicialSet.circle.{u} B)).mp
  apply MonoidalClosed.uncurry_injective
  apply rawCofiberCylinder_hom_ext (boundary.{u} 1).ι A
  · exact h
  · exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint PointedSimplicialSet.circle.{u} B f).trans
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint PointedSimplicialSet.circle.{u} B g).symm

/-- 元の区間族を同じ向きで回収する射は、構成した loop 射に厳密に一致する。 -/
lemma loopOfCylinder_unique {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁)
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right)
    (hf : (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      MonoidalClosed.uncurry (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ h) : f = loopOfCylinder B h h₀ h₁ := by
  apply loop_interval_hom_ext
  exact hf.trans (loopOfCylinder_raw B h h₀ h₁).symm

end SerrePositivity.KST.SConstruction
