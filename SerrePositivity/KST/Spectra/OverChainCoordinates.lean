module

public import SerrePositivity.KST.Spectra.CosimplicialLastVertex

/-!
概要：over 圏の nerve の単体を、底の射列と最後の係数射で表示する。
方針：忘却した射列と終点への最後の射を取り、可換三角形で全成分を復元する。
規約：任意の小圏で成立する厳密な集合の同値。
使われ方：Goerss–Jardine VII §4。BK 重みの各次数の representable 表示と Reedy latching の計算。
-/

@[expose] public section
universe u
open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.OverChainCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [SmallCategory C] {j : C} {n : ℕ}

/-- 底の射列と最後の対象から終点への射から over 圏の射列を復元する。 -/
def reconstruct (σ : ComposableArrows C n) (f : σ.obj (Fin.last n) ⟶ j) :
    ComposableArrows (Over j) n :=
  σ.toOver j (fun k ↦ σ.map (homOfLE (Fin.le_last k)) ≫ f) (by
    intro k l g
    rw [← Category.assoc, ← Functor.map_comp]
    rfl)

/-- 復元した射列を忘却すると指定した底の射列そのもの。 -/
lemma reconstruct_forget (σ : ComposableArrows C n) (f : σ.obj (Fin.last n) ⟶ j) :
    reconstruct σ f ⋙ Over.forget j = σ := rfl

/-- 復元した最後の対象の係数射は指定した射そのもの。 -/
lemma reconstruct_last (σ : ComposableArrows C n) (f : σ.obj (Fin.last n) ⟶ j) :
    ((reconstruct σ f).obj (Fin.last n)).hom = f := by
  change σ.map (𝟙 (Fin.last n)) ≫ f = f
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- 忘却した射列と最後の射から元の over 圏の射列が厳密に戻る。 -/
lemma reconstruct_coordinates (σ : ComposableArrows (Over j) n) :
    reconstruct (σ ⋙ Over.forget j) (σ.obj (Fin.last n)).hom = σ := by
  have h (k : Fin (n + 1)) :
      (reconstruct (σ ⋙ Over.forget j) (σ.obj (Fin.last n)).hom).obj k = σ.obj k := by
    change Over.mk ((σ.map (homOfLE (Fin.le_last k))).left ≫
      (σ.obj (Fin.last n)).hom) = σ.obj k
    rw [Over.w]
    rfl
  apply ComposableArrows.ext h
  intro i hi
  apply Over.OverMorphism.ext
  simp only [reconstruct, Functor.toOver_map_left, Functor.comp_map, Over.forget_map]
  simp

/-- over 圏の nerve の n 単体の representable 座標表示。 -/
def equiv (j : C) (n : ℕ) : ComposableArrows (Over j) n ≃
    Σ σ : ComposableArrows C n, σ.obj (Fin.last n) ⟶ j where
  toFun σ := ⟨σ ⋙ Over.forget j, (σ.obj (Fin.last n)).hom⟩
  invFun σ := reconstruct σ.1 σ.2
  left_inv := reconstruct_coordinates
  right_inv σ := by
    rcases σ with ⟨σ, f⟩
    exact Sigma.ext rfl (heq_of_eq (reconstruct_last σ f))

/-- 終点の射への作用は representable 座標の最後の射の後合成。 -/
lemma equiv_postcompose {j k : C} (f : j ⟶ k)
    (σ : ComposableArrows (Over j) n) :
    equiv k n (σ ⋙ Over.map f) =
      ⟨(equiv j n σ).1, (equiv j n σ).2 ≫ f⟩ := rfl

/-- 底の射列ごとの共変 representable の直和としての座標図式。 -/
def coordinateDiagram (C : Type u) [SmallCategory C] (n : ℕ) : C ⥤ Type u where
  obj j := Σ σ : ComposableArrows C n, σ.obj (Fin.last n) ⟶ j
  map f := ↾fun σ ↦ ⟨σ.1, σ.2 ≫ f⟩
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro ⟨σ, f⟩
    change (⟨σ, f ≫ 𝟙 j⟩ : Σ σ : ComposableArrows C n, σ.obj (Fin.last n) ⟶ j) = ⟨σ, f⟩
    rw [Category.comp_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro ⟨σ, h⟩
    change (⟨σ, h ≫ (f ≫ g)⟩ : Σ σ : ComposableArrows C n, σ.obj (Fin.last n) ⟶ _) =
      ⟨σ, (h ≫ f) ≫ g⟩
    rw [Category.assoc]

/-- BK 重みの各単体次数は終点の変数について representable の直和と自然同型。 -/
def degreeIso (C : Type u) [SmallCategory C] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight C ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋n⦌) ≅
    coordinateDiagram C n :=
  NatIso.ofComponents (fun j ↦ (equiv j n).toIso) (fun f ↦ by
    apply ConcreteCategory.hom_ext
    intro σ
    rfl)

end SerrePositivity.KST.Spectra.OverChainCoordinates
