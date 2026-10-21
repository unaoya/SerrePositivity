module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHom

/-! # 次元を固定した元の鎖 tensor の関手性
概要：元の左右の鎖射の tensor が恒等・合成を保つことを、四対象を保持して回収する。
方針：抽象モノイダル圏の元の法則を適用する。
規約：次元を tensor の値から逆に推測しない。使われ方：連結比較の全生成射への拡張。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の左右の恒等射の鎖 tensor は恒等射。 -/
lemma serreCubeTensorHom_id (n m : ℕ) :
    serreCubeTensorHom A (𝟙 (serreCubeComonoid A n)) (𝟙 (serreCubeComonoid A m)) =
      𝟙 (serreCubeComonoid A n ⊗ serreCubeComonoid A m) :=
  MonoidalCategory.id_tensorHom_id _ _

/-- 元の左右の合成の鎖 tensor は、同じ鎖 tensor 射の合成。 -/
lemma serreCubeTensorHom_comp {n p r m q s : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A p)
    (f' : serreCubeComonoid A p ⟶ serreCubeComonoid A r)
    (g : serreCubeComonoid A m ⟶ serreCubeComonoid A q)
    (g' : serreCubeComonoid A q ⟶ serreCubeComonoid A s) :
    serreCubeTensorHom A (n := n) (p := r) (m := m) (q := s) (f ≫ f') (g ≫ g') =
      serreCubeTensorHom A (n := n) (p := p) (m := m) (q := q) f g ≫
        serreCubeTensorHom A (n := p) (p := r) (m := q) (q := s) f' g' :=
  (MonoidalCategory.tensorHom_comp_tensorHom f g f' g').symm

end SerrePositivity.KST.SConstruction
