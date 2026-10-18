module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：KST §3.1 の diagram-module 係数圏で使う、係数遷移後の乗法の法則。
方針：モノイド対象の射で最初の係数を送り、目標の積で合成する。
規約：一般のモノイダル圏で示し、dg 複体へ適用する。
使われ方：diagram-module 係数 dg 圏の単位・結合律。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 概要：係数を目標代数へ送ってから掛ける合成射。
方針：代数射を最初の因子に作用させて目標の乗法を適用する。
規約：KST §3.1。使われ方：包含に対応する Hom の合成。 -/
def diagramAlgebraMul {A B : Mon C} (f : A ⟶ B) : A.X ⊗ B.X ⟶ B.X :=
  (f.hom ⊗ₘ 𝟙 _) ≫ MonObj.mul

/-- 概要：係数遷移後の乗法は最初の代数の単位を左単位にする。
方針：代数射の単位保存を使って目標代数の左単位律へ帰着する。
規約：KST §3.1。使われ方：diagram-module 係数圏の左単位律。 -/
@[reassoc] theorem diagramAlgebraMul_one {A B : Mon C} (f : A ⟶ B) :
    MonObj.one (X := A.X) ▷ B.X ≫ diagramAlgebraMul f = (λ_ B.X).hom := by
  unfold diagramAlgebraMul
  rw [tensorHom_id, ← comp_whiskerRight_assoc, IsMonHom.one_hom, MonObj.one_mul]

/-- 概要：恒等係数遷移後の乗法は元の代数の乗法に一致する。
方針：恒等射の tensor と合成を簡約する。
規約：KST §3.1。使われ方：diagram-module 係数圏の右単位律。 -/
theorem diagramAlgebraMul_id (A : Mon C) : diagramAlgebraMul (𝟙 A) = MonObj.mul := by
  simp [diagramAlgebraMul]

/-- 概要：二段の係数遷移後の乗法は結合的。
方針：代数射の積保存で目標代数の三重積へ移し、その結合律と tensor の自然性を使う。
規約：KST §3.1。使われ方：diagram-module 係数 dg 圏の結合律。 -/
theorem diagramAlgebraMul_assoc {A B D : Mon C} (f : A ⟶ B) (g : B ⟶ D) :
    diagramAlgebraMul f ▷ D.X ≫ diagramAlgebraMul g =
      (α_ A.X B.X D.X).hom ≫ A.X ◁ diagramAlgebraMul g ≫ diagramAlgebraMul (f ≫ g) := by
  unfold diagramAlgebraMul
  simp only [tensorHom_id]
  calc
    ((f.hom ▷ B.X ≫ MonObj.mul) ▷ D.X) ≫ g.hom ▷ D.X ≫ MonObj.mul =
        (f.hom ▷ B.X) ▷ D.X ≫ (g.hom ⊗ₘ g.hom) ▷ D.X ≫
          MonObj.mul ▷ D.X ≫ MonObj.mul := by
      simpa only [comp_whiskerRight, Category.assoc] using
        congrArg (fun t => (f.hom ▷ B.X) ▷ D.X ≫ t)
          (congrArg (fun t => t ▷ D.X ≫ MonObj.mul) (IsMonHom.mul_hom g.hom))
    _ = ((f.hom ≫ g.hom ⊗ₘ g.hom) ▷ D.X) ≫
        MonObj.mul ▷ D.X ≫ MonObj.mul := by
      rw [← comp_whiskerRight_assoc, ← tensorHom_id f.hom,
        tensorHom_comp_tensorHom, Category.id_comp]
    _ = ((f.hom ≫ g.hom ⊗ₘ g.hom) ▷ D.X) ≫
        (α_ D.X D.X D.X).hom ≫ D.X ◁ MonObj.mul ≫ MonObj.mul := by
      rw [MonObj.mul_assoc]
    _ = _ := by
      change _ = (α_ A.X B.X D.X).hom ≫ A.X ◁ (g.hom ▷ D.X ≫ MonObj.mul) ≫
        (f.hom ≫ g.hom) ▷ D.X ≫ MonObj.mul
      rw [← tensorHom_id (f.hom ≫ g.hom ⊗ₘ g.hom), associator_naturality_assoc]
      rw [tensorHom_def']
      simp only [Category.assoc, tensorHom_id]
      rw [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc]

end SerrePositivity.KST.DerivedBlowup
