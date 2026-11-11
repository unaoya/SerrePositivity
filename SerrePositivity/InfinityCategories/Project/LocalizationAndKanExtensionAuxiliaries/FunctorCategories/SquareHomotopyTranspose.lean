module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFunctorSquare

/-!
概要：関手正方形のホモトピーを、時間をパラメータに含めた正方形へ転置する。
方針：パラメータ・時間・正方形の順をパラメータ・正方形・時間へ並べ替えて curry する。
規約：時間の両端と固定した辺の raw な図式を回収する。
使われ方：B1 の正方形の復元比較を comma の写像空間の族のホモトピーへ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：パラメータ・時間・図式の座標をパラメータ・図式・時間へ並べ替える。
方針：各次数で直積の成分を入れ替える。
規約：時間は Δ[1]。
使われ方：正方形のホモトピーを時間付きの族にする。 -/
def diagramTimeSwap (A K : SSet.{u}) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ K ⟶ A ⊗ (K ⊗ (Δ[1] : SSet.{u})) where
  app _ := ↾fun p ↦ (p.1.1, (p.2, p.1.2))
  naturality {_ _} _ := rfl

/-- 概要：図式の時間ホモトピーを時間付きパラメータの図式へ転置する。
方針：uncurry の後で時間を入れ替え、再び curry する。
規約：図式の始域 K は任意。
使われ方：正方形の四辺と時間端点を同時に検証する。 -/
def diagramHomotopyTranspose {A K X : SSet.{u}}
    (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X) : K ⟶ (ihom (A ⊗ (Δ[1] : SSet.{u}))).obj X :=
  curry (diagramTimeSwap A K ≫ uncurry H)

/-- 概要：固定部分図式の転置は時間を忘れる前合成に一致する。
方針：元の相対条件を uncurry し、同じ三成分で評価する。
規約：固定条件はホモトピー類でなく raw な射の等式。
使われ方：正方形の三辺・全境界の固定を時間付き正方形へ移す。 -/
lemma diagramHomotopyTranspose_restriction {A K L X : SSet.{u}}
    (H : K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X) (e : L ⟶ K) (b : L ⟶ (ihom A).obj X)
    (h : (e ▷ (Δ[1] : SSet.{u})) ≫ H = fst L (Δ[1] : SSet.{u}) ≫ b) :
    e ≫ diagramHomotopyTranspose H = b ≫ (pre (fst A (Δ[1] : SSet.{u}))).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left, diagramHomotopyTranspose, uncurry_curry, uncurry_pre_app]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨a, t⟩, k⟩
  change (uncurry H).app n (a, (e.app n k, t)) = (uncurry b).app n (a, k)
  have hh := congrArg
    (fun F : L ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X ↦ (uncurry F).app n (a, (k, t))) h
  rw [uncurry_natural_left, uncurry_natural_left] at hh
  exact hh

/-- 概要：転置した図式を時間零で制限すると元の始点図式。
方針：時間端点の等式を uncurry して同じパラメータで評価する。
規約：実際の図式を厳密に回収する。
使われ方：時間付き comma 正方形の始点の回収。 -/
lemma diagramHomotopyTranspose_zero {A K X : SSet.{u}}
    {f g : K ⟶ (ihom A).obj X} (H : SSet.Homotopy f g) :
    diagramHomotopyTranspose H.h ≫ (pre (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u}))).app X = f := by
  apply uncurry_injective
  rw [uncurry_pre_app, diagramHomotopyTranspose, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, k⟩
  change (uncurry H.h).app n (a, (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n k) =
    (uncurry f).app n (a, k)
  have hh := congrArg (fun F : K ⟶ (ihom A).obj X ↦ (uncurry F).app n (a, k)) H.h₀
  rw [uncurry_natural_left] at hh
  exact hh

/-- 概要：転置した図式を時間一で制限すると元の終点図式。
方針：時間端点の等式を uncurry して同じパラメータで評価する。
規約：実際の図式を厳密に回収する。
使われ方：時間付き comma 正方形の終点の回収。 -/
lemma diagramHomotopyTranspose_one {A K X : SSet.{u}}
    {f g : K ⟶ (ihom A).obj X} (H : SSet.Homotopy f g) :
    diagramHomotopyTranspose H.h ≫ (pre (SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u}))).app X = g := by
  apply uncurry_injective
  rw [uncurry_pre_app, diagramHomotopyTranspose, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, k⟩
  change (uncurry H.h).app n (a, (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})).app n k) =
    (uncurry g).app n (a, k)
  have hh := congrArg (fun F : K ⟶ (ihom A).obj X ↦ (uncurry F).app n (a, k)) H.h₁
  rw [uncurry_natural_left] at hh
  exact hh

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
