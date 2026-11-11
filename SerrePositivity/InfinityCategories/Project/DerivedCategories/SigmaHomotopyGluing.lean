module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutHomotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 余積セル族の全時刻の貼り合わせ

概要：余積の各成分上の実ホモトピーを、同じ端点を保った余積上の実ホモトピーへ貼る。
方針：区間との直積が余積を保つことから、全時間の射を余積の普遍性で組み立てる。
規約：成分への制限は厳密な等式。使われ方：有限相対骨格のセル比較の同時貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial
variable {I : Type u} (X : I → SSet.{u}) {Y : SSet.{u}}

/-- 区間との直積後の余積の余錐は余極限である。 -/
def sigmaTensorIsColimit : IsColimit
    (Cofan.mk ((∐ X) ⊗ (Δ[1] : SSet.{u})) (fun i => Sigma.ι X i ▷ Δ[1])) :=
  isColimitCofanMkObjOfIsColimit (tensorRight (Δ[1] : SSet.{u})) X
    (fun i => Sigma.ι X i) (coproductIsCoproduct X)

/-- 余積セル上の全時刻の射を貼り合わせる。 -/
def sigmaTensorGlue (H : ∀ i, X i ⊗ (Δ[1] : SSet.{u}) ⟶ Y) :
    (∐ X) ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  Cofan.IsColimit.desc (sigmaTensorIsColimit X) H

/-- 各セルへの制限は指定された同じ全時刻の射。 -/
lemma sigmaTensorGlue_ι (H : ∀ i, X i ⊗ (Δ[1] : SSet.{u}) ⟶ Y) (i : I) :
    (Sigma.ι X i ▷ (Δ[1] : SSet.{u})) ≫ sigmaTensorGlue X H = H i :=
  Cofan.IsColimit.fac (sigmaTensorIsColimit X) H i

/-- 余積と区間の積からの射は各セル上で厳密に決まる。 -/
lemma sigmaTensor_hom_ext {f g : (∐ X) ⊗ (Δ[1] : SSet.{u}) ⟶ Y}
    (h : ∀ i, (Sigma.ι X i ▷ (Δ[1] : SSet.{u})) ≫ f =
      (Sigma.ι X i ▷ (Δ[1] : SSet.{u})) ≫ g) : f = g :=
  (sigmaTensorIsColimit X).hom_ext (fun ⟨i⟩ => h i)

/-- 各セル上の実ホモトピーを同じ二端点を保って余積へ貼る。 -/
def sigmaHomotopyGlue {f g : (∐ X) ⟶ Y}
    (H : ∀ i, SSet.Homotopy (Sigma.ι X i ≫ f) (Sigma.ι X i ≫ g)) : SSet.Homotopy f g where
  h := sigmaTensorGlue X (fun i => (H i).h)
  h₀ := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, sigmaTensorGlue_ι]
    exact (H i).h₀
  h₁ := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, sigmaTensorGlue_ι]
    exact (H i).h₁
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 貼り合わせたホモトピーは各成分のホモトピーを厳密に再現する。 -/
lemma sigmaHomotopyGlue_ι {f g : (∐ X) ⟶ Y}
    (H : ∀ i, SSet.Homotopy (Sigma.ι X i ≫ f) (Sigma.ι X i ≫ g)) (i : I) :
    (Sigma.ι X i ▷ (Δ[1] : SSet.{u})) ≫ (sigmaHomotopyGlue X H).h = (H i).h :=
  sigmaTensorGlue_ι X (fun i => (H i).h) i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
