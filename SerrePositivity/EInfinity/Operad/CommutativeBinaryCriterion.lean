module

public import SerrePositivity.EInfinity.Operad.CommutativeAlgebraGeneration

/-!
# 通常の単位と二項積による Com 代数射の判定

概要：係数単位と余分な冪単位を除いた零入力・二入力の保存で全作用を判定する。
方針：単位子の自然性で元の全入力生成補題へ帰着する。
規約：底の射と元の Com 作用を保持する。
使われ方：標準 H⁰ 同型を全 arity の代数同型へ上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Algebra
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]
attribute [local implicit_reducible] TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

def commutativeUnit (X : (commutativeOperad A).Algebra) :
    𝟙_ (Complex A) ⟶ X.carrier := (λ_ (power X.carrier 0)).inv ≫ X.action 0

def commutativeBinary (X : (commutativeOperad A).Algebra) :
    X.carrier ⊗ X.carrier ⟶ X.carrier :=
  (X.carrier ◁ (oneIso X.carrier).inv) ≫
    (λ_ (power X.carrier 2)).inv ≫ X.action 2

lemma binaryInput_naturality {X Y : Complex A} (f : X ⟶ Y) :
    (X ◁ (oneIso X).inv) ≫ TensorPowers.map f 2 =
      (f ⊗ₘ f) ≫ (Y ◁ (oneIso Y).inv) := by
  have hn := ((oneNatIso (C := Complex A)).inv.naturality f).symm
  change (oneIso X).inv ≫ TensorPowers.map f 1 = f ≫ (oneIso Y).inv at hn
  change (X ◁ (oneIso X).inv) ≫ (f ⊗ₘ TensorPowers.map f 1) = _
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, hn]
  rw [← id_tensorHom Y (oneIso Y).inv, tensorHom_comp_tensorHom, Category.comp_id]

def commutativeHomOfUnitBinary (X Y : (commutativeOperad A).Algebra)
    (f : X.carrier ⟶ Y.carrier)
    (h0 : commutativeUnit X ≫ f = commutativeUnit Y)
    (h2 : commutativeBinary X ≫ f = (f ⊗ₘ f) ≫ commutativeBinary Y) : X ⟶ Y := by
  apply commutativeHomOfZeroTwo X Y f
  · apply (cancel_epi (λ_ (power X.carrier 0)).inv).mp
    change (λ_ (𝟙_ (Complex A))).inv ≫ (X.action 0 ≫ f) =
      (λ_ (𝟙_ (Complex A))).inv ≫ ((𝟙_ (Complex A) ◁ 𝟙 (𝟙_ (Complex A))) ≫ Y.action 0)
    simp only [whiskerLeft_id, Category.id_comp]
    exact h0
  · apply (cancel_epi ((X.carrier ◁ (oneIso X.carrier).inv) ≫
      (λ_ (power X.carrier 2)).inv)).mp
    simp only [Category.assoc]
    erw [← leftUnitor_inv_naturality_assoc, reassoc_of% (binaryInput_naturality f)]
    exact h2

end SerrePositivity.EInfinity.Operad.Algebra
