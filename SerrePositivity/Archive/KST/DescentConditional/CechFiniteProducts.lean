module

public import SerrePositivity.KST.Descent.FiniteProductTensor
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightComparison

/-!
# 有限積による単体集合の弱同値の保存

## 概要
有限被覆族の Čech 各段の有限積は、成分ごとの実際の弱同値を保つことを証明する。

## 方針
cofibration が単射であることから全空間の cofibrancy を導く。
Cartesian テンソルの左右の左 Quillen 性から二項積の場合を証明し、有限添字に帰納する。

## 規約
右 Quillen 関手が全ての弱同値を保つとは仮定しない。元の空間の fibrancy は不要。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の空の多重交叉を除く計算。
原典の τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

variable [ModelCategory SSet.{u}] [IsQuillenBifunctor (curriedTensor SSet.{u})]
  (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)

include hcof in
/-- 概要：二つの弱同値の Cartesian テンソルは弱同値（公理 (1)）。
方針：全単体集合の cofibrancy と、左右のテンソルの左 Quillen 性を使う。
規約：fibrancy は不要。使われ方：被覆族の有限積の帰納。 -/
theorem cechTensor_weak {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : weakEquivalences SSet.{u} f) (hg : weakEquivalences SSet.{u} g) :
    weakEquivalences SSet.{u} (f ⊗ₘ g) := by
  have := WeightComparison.all_cofibrant hcof X
  have := WeightComparison.all_cofibrant hcof X'
  have := WeightComparison.all_cofibrant hcof Y
  have := WeightComparison.all_cofibrant hcof Y'
  have : WeakEquivalence f := ⟨hf⟩
  have : WeakEquivalence g := ⟨hg⟩
  have := tensorRight_isLeftQuillen Y
  have := tensorLeft_isLeftQuillen X'
  have : WeakEquivalence ((tensorRight Y).map f) := map_weakEquivalence_of_cofibrant _ f
  have : WeakEquivalence ((tensorLeft X').map g) := map_weakEquivalence_of_cofibrant _ g
  rw [tensorHom_def]
  exact (weakEquivalences SSet.{u}).comp_mem _ _
    (mem_weakEquivalences ((tensorRight Y).map f))
    (mem_weakEquivalences ((tensorLeft X').map g))

include hcof in
/-- 概要：有限積は成分ごとの実際の弱同値を保つ（公理 (1)）。
方針：空積の一意性、Option の指定テンソル分解、添字の同値で有限帰納する。
規約：任意の有限添字の universe で成立。使われ方：空の交叉の値を終対象で置換する Čech 比較。 -/
theorem cechFiniteProduct_weak {ι : Type v} [Finite ι]
    {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, weakEquivalences SSet.{u} (f i)) :
    weakEquivalences SSet.{u} (CategoryTheory.Limits.Pi.map f) := by
  let P := fun κ : Type v ↦ ∀ [Finite κ] (A B : κ → SSet.{u})
    (g : ∀ i, A i ⟶ B i), (∀ i, weakEquivalences SSet.{u} (g i)) →
      weakEquivalences SSet.{u} (CategoryTheory.Limits.Pi.map g)
  have h : P ι := by
    apply Finite.induction_empty_option
    · intro α β e ih hβ A B g hg
      let : Finite α := Finite.of_equiv β e.symm
      let eA := Pi.reindex e A
      let eB := Pi.reindex e B
      have hn : CategoryTheory.Limits.Pi.map (fun i ↦ g (e i)) ≫ eB.hom =
          eA.hom ≫ CategoryTheory.Limits.Pi.map g := by
        apply Pi.hom_ext
        intro i
        obtain ⟨j, rfl⟩ := e.surjective i
        simp only [Category.assoc, Pi.map_π, eA, eB,
          Pi.reindex_hom_π, Pi.reindex_hom_π_assoc]
        exact Pi.map_π (fun i ↦ g (e i)) j
      have hw := ih (A ∘ e) (B ∘ e) (fun i ↦ g (e i)) (fun i ↦ hg (e i))
      have hc := (weakEquivalences SSet.{u}).comp_mem _ _ hw
        (mem_weakEquivalences eB.hom)
      rw [hn] at hc
      exact (weakEquivalences SSet.{u}).of_precomp _ _ (mem_weakEquivalences eA.hom) hc
    · intro _ A B g _
      have ha : IsTerminal (∏ᶜ A) := IsTerminal.ofUniqueHom
        (fun Z ↦ Pi.lift fun i ↦ i.elim) (by intro Z f; apply Pi.hom_ext; intro i; exact i.elim)
      have hb : IsTerminal (∏ᶜ B) := IsTerminal.ofUniqueHom
        (fun Z ↦ Pi.lift fun i ↦ i.elim) (by intro Z f; apply Pi.hom_ext; intro i; exact i.elim)
      have : IsIso (CategoryTheory.Limits.Pi.map g) := isIso_of_isTerminal ha hb _
      exact mem_weakEquivalences _
    · intro α _ ih _ A B g hg
      have hw := cechTensor_weak hcof (g none)
        (CategoryTheory.Limits.Pi.map (fun i ↦ g (some i))) (hg none)
        (ih (fun i ↦ A (some i)) (fun i ↦ B (some i)) (fun i ↦ g (some i))
          (fun i ↦ hg (some i)))
      have hc := (weakEquivalences SSet.{u}).comp_mem _ _
        (mem_weakEquivalences (optionProductTensorIso A).hom) hw
      rw [← optionProductTensorIso_naturality] at hc
      exact (weakEquivalences SSet.{u}).of_postcomp _ _
        (mem_weakEquivalences (optionProductTensorIso B).hom) hc
  exact h X Y f hf

end SerrePositivity.KST.Descent
