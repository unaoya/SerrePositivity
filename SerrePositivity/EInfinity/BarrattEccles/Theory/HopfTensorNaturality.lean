module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorOperations

/-!
# Hopf テンソル演算の射に関する自然性

## 概要
HA 3.2.4.7 の全関手比較のため、BF §1.1.4 のテンソル演算を全ての代数射で比較する。

## 方針
テンソル冪の二列分離の自然性と、各因子の作用の保存則を合成する。

## 規約
自然性は指定された複体射の等式であり、点ごとの同型の選択は使わない。

## 使われ方
テンソル代数の二変数の射と、局所化へ降ろす比較の自然変換。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- BF §1.1.4 の二列分離は二つの複体射に自然。 -/
@[reassoc]
lemma tensorPowerSeparation_naturality {V W V' W' : Complex A}
    (f : V ⟶ V') (g : W ⟶ W') (n : ℕ) :
    map (f ⊗ₘ g) n ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V' W' n).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom ≫ (map f n ⊗ₘ map g n) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ (λ_ (𝟙_ (Complex A))).inv =
      (λ_ (𝟙_ (Complex A))).inv ≫ (𝟙 _ ⊗ₘ 𝟙 _)
    rw [Category.id_comp, tensorHom_id, id_whiskerRight, Category.comp_id]
  | succ n ih =>
    simp only [map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
    rw [tensorHom_comp_whiskerLeft_assoc, ih, ← whiskerLeft_comp_tensorHom_assoc]
    exact congrArg (fun k => ((V ⊗ W) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom) ≫ k)
      (tensorμ_natural f g (map f n) (map g n))

/-- BF §1.1.4 のテンソル演算は両因子の全ての代数射と可換。 -/
lemma hopfTensorAction_naturality (hP : P.Hopf) {X Y X' Y' : P.Algebra}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    hopfTensorAction hP X Y n ≫ (f.hom ⊗ₘ g.hom) =
      (𝟙 (P.arity n) ⊗ₘ map (f.hom ⊗ₘ g.hom) n) ≫
        hopfTensorAction hP X' Y' n := by
  have hf := f.comm n
  have hg := g.comm n
  simp only [id_tensorHom] at hf hg
  symm
  unfold hopfTensorAction
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp,
    tensorPowerSeparation_naturality, ← tensorHom_comp_whiskerLeft_assoc,
    tensorμ_natural_right_assoc, tensorHom_comp_tensorHom, ← hf, ← hg,
    ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

end SerrePositivity.EInfinity
