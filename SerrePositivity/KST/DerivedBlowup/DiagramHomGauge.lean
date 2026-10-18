module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraMultiplication
public import SerrePositivity.KST.DerivedBlowup.DGEndMonoid
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：KST §3.1 の捻りを係数 dg 圏の自己関手にするための Hom 自己同型データ。
方針：各包含の目標複体の自己同型と、単位・係数遷移後の積との整合性を持つ。
規約：このデータの具体値には全ての整合性の証明が必要であり、公理として供給しない。
使われ方：推移単元の整数冪による O(m) の実際の dg 図式加群。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J]

/-- 概要：指定係数図式の Hom を重み付けする自己同型と整合性の証明。
方針：対角は恒等、二つの包含の積では係数遷移後の乗法と可換と要求する。
規約：KST §3.1。使われ方：構成済み係数 dg 圏の自己関手を実際に作る入力。 -/
structure DiagramHomGauge (F : J ⥤ Mon (Complex R)) where
  scale {i j : J} (h : i ≤ j) : (F.obj j).X ≅ (F.obj j).X
  scale_id (i : J) : scale (le_refl i) = Iso.refl _
  scale_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    ((scale h).hom ⊗ₘ (scale g).hom) ≫ diagramAlgebraMul (F.map (homOfLE g)) =
      diagramAlgebraMul (F.map (homOfLE g)) ≫ (scale (h.trans g)).hom

variable (F : J ⥤ Mon (Complex R))

/-- 概要：全ての包含で恒等な Hom 自己同型データ。
方針：恒等射の tensor と合成の単位律を使う。
規約：KST §3.1。使われ方：零捻りの基準。 -/
def diagramHomGaugeIdentity : DiagramHomGauge F where
  scale _ := Iso.refl _
  scale_id _ := rfl
  scale_comp _ _ := by simp

/-- 概要：二つの証明済み Hom 自己同型データの合成。
方針：各包含で自然同型を合成し、二つの乗法整合式を続けて使う。
規約：KST §3.1。使われ方：捻りの和に対応する自己関手の合成。 -/
def DiagramHomGauge.comp (s t : DiagramHomGauge F) : DiagramHomGauge F where
  scale h := s.scale h ≪≫ t.scale h
  scale_id i := by simp only [s.scale_id, t.scale_id, Iso.refl_trans]
  scale_comp h g := by
    simp only [Iso.trans_hom]
    rw [← tensorHom_comp_tensorHom_assoc, t.scale_comp, ← Category.assoc,
      s.scale_comp, Category.assoc]

end SerrePositivity.KST.DerivedBlowup
