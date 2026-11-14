module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedTensor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# 自由整数単体的加群のテンソル区間

概要：非被約な自由加群を始域とするテンソル区間ホモトピーを定義する。
方針：積の自由化との同型で両端を移送し、次数制限を明示する。
規約：KST Definition A.3。作用の同変性は別に検証する条件であり、この基礎定義には含めない。
使われ方：Construction A.6 の全次数ホモトピーと A.5 の部分次数比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

/-- 概要：非被約な自由加群と自由区間のテンソル。
方針：各次数の整数加群のテンソル。
規約：KST Definition A.3 の C⊗ℤΔ¹。
使われ方：全次数および次数制限つきのホモトピーの始域。 -/
abbrev linearizedCylinder (X : SSet.{u}) :=
  simplicialIntegerTensor (linearizedSpace X) (linearizedSpace (Δ[1] : SSet.{u}))

/-- 概要：テンソル区間の零端点。
方針：幾何的な端点包含の自由化をテンソル同型の逆で移す。
規約：KST Definition A.3。使われ方：ホモトピーの始点条件。 -/
def linearizedEndpoint₀ (X : SSet.{u}) : linearizedSpace X ⟶ linearizedCylinder X :=
  linearizedSpaceMap SSet.ι₀ ≫ (linearizedTensorIso X Δ[1]).inv

/-- 概要：テンソル区間の一端点。
方針：幾何的な端点包含の自由化をテンソル同型の逆で移す。
規約：KST Definition A.3。使われ方：ホモトピーの終点条件。 -/
def linearizedEndpoint₁ (X : SSet.{u}) : linearizedSpace X ⟶ linearizedCylinder X :=
  linearizedSpaceMap SSet.ι₁ ≫ (linearizedTensorIso X Δ[1]).inv

/-- 概要：非被約な自由整数加群を始域とする全次数の区間ホモトピー。
方針：C⊗ℤΔ¹ からの単体的加群射と両端の等式を保持する。
規約：KST Definition A.3 の次数制限を外した基礎型。同変性は別条件。
使われ方：Construction A.6 の結論と、その次数制限。 -/
structure LinearizedHomotopy {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    (f g : linearizedSpace X ⟶ D) where
  h : linearizedCylinder X ⟶ D
  h₀ : linearizedEndpoint₀ X ≫ h = f
  h₁ : linearizedEndpoint₁ X ≫ h = g

/-- 概要：m 次まで両端を指定した単体的加群の区間ホモトピー。
方針：区間写像は全次数で定義し、両端の等式だけを制限する。
規約：KST Definition A.3 の非同変な基礎型。零次を含む。
使われ方：A.5 と A.4 の同変版の下層の比較。 -/
structure LinearizedMHomotopy {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    (f g : linearizedSpace X ⟶ D) (m : ℕ) where
  h : linearizedCylinder X ⟶ D
  h₀ (n : ℕ) (hn : n ≤ m) : (linearizedEndpoint₀ X ≫ h).app (op ⦋n⦌) = f.app (op ⦋n⦌)
  h₁ (n : ℕ) (hn : n ≤ m) : (linearizedEndpoint₁ X ≫ h).app (op ⦋n⦌) = g.app (op ⦋n⦌)

/-- 概要：全次数ホモトピーは任意の m 次ホモトピーを与える。
方針：自然変換の両端等式を各次数で評価する。
規約：KST Definition A.3。使われ方：Construction A.6 の次数制限。 -/
def LinearizedHomotopy.truncate {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    {f g : linearizedSpace X ⟶ D} (H : LinearizedHomotopy f g) (m : ℕ) :
    LinearizedMHomotopy f g m where
  h := H.h
  h₀ n _ := congrArg (fun a ↦ a.app (op ⦋n⦌)) H.h₀
  h₁ n _ := congrArg (fun a ↦ a.app (op ⦋n⦌)) H.h₁

/-- 概要：幾何的ホモトピーをテンソル区間の自由整数加群ホモトピーへ移す。
方針：積とテンソルの同型を自由化した区間写像に前合成する。
規約：KST Construction A.6、非被約 C(H)。
使われ方：共役の実ホモトピーを Definition A.3 の界面へ移す。 -/
def linearizedTensorHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    LinearizedHomotopy (linearizedSpaceMap f) (linearizedSpaceMap g) where
  h := (linearizedTensorIso X Δ[1]).hom ≫ linearizedSpaceMap H.h
  h₀ := by
    simp only [linearizedEndpoint₀, Category.assoc, Iso.inv_hom_id_assoc]
    change ((SimplicialObject.whiskering _ _).obj integerLinearization).map SSet.ι₀ ≫
      ((SimplicialObject.whiskering _ _).obj integerLinearization).map H.h = _
    rw [← Functor.map_comp, H.h₀]
  h₁ := by
    simp only [linearizedEndpoint₁, Category.assoc, Iso.inv_hom_id_assoc]
    change ((SimplicialObject.whiskering _ _).obj integerLinearization).map SSet.ι₁ ≫
      ((SimplicialObject.whiskering _ _).obj integerLinearization).map H.h = _
    rw [← Functor.map_comp, H.h₁]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Def A.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy
