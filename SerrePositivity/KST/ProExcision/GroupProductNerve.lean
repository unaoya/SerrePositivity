module
public import SerrePositivity.KST.ProExcision.GroupProductData
public import Mathlib.CategoryTheory.Products.Basic

/-!
# 明示的な群の積の準同型の nerve への適用

概要：二つの群の nerve の単体の対を直積の圏の単体へ送り、最後に μ を適用する。
方針：ComposableArrows の二つの関手を点ごとの積にし、群準同型の関手へ後合成する。
規約：KST Construction A.5 の修正形。標的 H の可換性を仮定しない。
使われ方：因子内のホモトピーの値域を保ったまま最後に μ を適用する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

/-- 概要：二つの nerve の単体の対を直積の圏の単体へ送る。
方針：二つの同じ有限順序集合上の関手の点ごとの積。
規約：KST A.5、圏の一般的な積を使う。
使われ方：群の直積へ入る前の実単体的写像。 -/
def nervePairMap (C D : Type v) [Category.{u} C] [Category.{u} D] :
    nerve C ⊗ nerve D ⟶ nerve (C × D) where
  app n := ↾fun z ↦ z.1.prod' z.2
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro z
    rfl

/-- 概要：群準同型 μ は二つの一対象圏の積から標的の一対象圏への関手を定める。
方針：射の対に μ を適用する。
規約：KST A.5 の修正形、H の可換性を不要にする明示的な μ。
使われ方：nerve の積の単体へ μ を最後に適用する。 -/
def groupProductFunctor {P Q H : Type u} [Group P] [Group Q] [Group H]
    (μ : P × Q →* H) : (SingleObj P × SingleObj Q) ⥤ SingleObj H where
  obj _ := PUnit.unit
  map z := μ (z.1, z.2)
  map_id _ := μ.map_one
  map_comp f g := μ.map_mul (g.1, g.2) (f.1, f.2)

/-- 概要：二つの群の nerve の積から μ の標的の nerve への実単体的写像。
方針：単体の対を直積の圏の単体へ送り、群準同型 μ の関手を適用する。
規約：KST Construction A.5 の修正形、原典の可換な H への置換を使わない。
使われ方：テンソルの実区間比較の最後の後合成。 -/
def groupProductNerve {P Q H : Type u} [Group P] [Group Q] [Group H]
    (μ : P × Q →* H) : nerve (SingleObj P) ⊗ nerve (SingleObj Q) ⟶ nerve (SingleObj H) :=
  nervePairMap (SingleObj P) (SingleObj Q) ≫ nerveMap (groupProductFunctor μ)

/-- 概要：任意の単体的集合の対角射。
方針：各単体を同じ単体の対へ送る。
規約：KST A.5。使われ方：二つの入力の共通の始域 T の対角。 -/
def simplicialDiagonal (X : SSet.{u}) : X ⟶ X ⊗ X where
  app n := ↾fun x ↦ (x, x)

/-- 概要：二つの群準同型を対角から μ へ送る実写像は合成準同型の nerve。
方針：ComposableArrows の関手の対象と射の定義を評価する。
規約：KST A.5 の μ 版、因子の群も標的も非可換でよい。
使われ方：テンソル比較の左辺と補正した三つの項の同定。 -/
lemma groupProductNerve_comp {T P Q H : Type u} [Group T] [Group P] [Group Q] [Group H]
    (μ : P × Q →* H) (α : T →* P) (β : T →* Q) :
    simplicialDiagonal (nerve (SingleObj T)) ≫
      (nerveMap (SingleObj.mapHom _ _ α) ⊗ₘ nerveMap (SingleObj.mapHom _ _ β)) ≫ groupProductNerve μ =
    nerveMap (SingleObj.mapHom _ _ (μ.comp (α.prod β))) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rfl

end SerrePositivity.KST.ProExcision
