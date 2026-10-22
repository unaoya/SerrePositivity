module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionProduct

/-!
概要：四辺を保つ経路 connection を実 dg 代数射として構成する。
方針：比較 cochain の積の式を両端の代数射の積保存と組み合わせる。
規約：非可換の元の乗法を保存する。使われ方：class 正方形の輪郭の乗法的比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

lemma connectionHom_product_comparison :
    (Cochain.ofHom (connectionHom R B ⊗ₘ connectionHom R B)).comp
      ((Cochain.ofHom μ[(algebra R (algebra R B)).X]).comp
        (primitive R (algebra R B)) (zero_add (-1))) (zero_add (-1)) =
      connectionProductCochain R B := by
  have hh : (Cochain.ofHom (connectionHom R B)).comp
      (primitive R (algebra R B)) (zero_add (-1)) =
      (connectionCochain R B).comp (Cochain.ofHom (𝟙 (algebra R B).X))
        (add_zero (-1)) := by rw [connectionHom_primitive, Cochain.comp_id]
  have hr := cochainRightProduct_natural (𝟙 (algebra R B)) (connectionHom R B)
    ((source R B).hom ≫ diagonalHom R B) (source R (algebra R B)).hom
    (by simpa only [Mon.id_hom', Category.comp_id] using connectionHom_source R B)
    (-1) (connectionCochain R B) (primitive R (algebra R B)) hh
  have hl := cochainLeftProduct_natural (𝟙 (algebra R B)) (connectionHom R B)
    (𝟙 (algebra R B).X) (target R (algebra R B)).hom
    (by simpa only [Mon.id_hom', Category.comp_id] using connectionHom_target R B)
    (-1) (connectionCochain R B) (primitive R (algebra R B)) hh
  rw [mul_primitive, Cochain.comp_add, hr, hl]
  simp only [connectionProductCochain, Mon.id_hom', Cochain.comp_id]

lemma connectionHom_mul : μ[(algebra R B).X] ≫ connectionHom R B =
    (connectionHom R B ⊗ₘ connectionHom R B) ≫ μ[(algebra R (algebra R B)).X] := by
  apply chain_ext R (algebra R B)
  · rw [Category.assoc, connectionHom_source, Category.assoc,
      IsMonHom.mul_hom (source R (algebra R B)).hom]
    rw [← Category.assoc (connectionHom R B ⊗ₘ connectionHom R B)
      ((source R (algebra R B)).hom ⊗ₘ (source R (algebra R B)).hom),
      tensorHom_comp_tensorHom, connectionHom_source]
    change μ[(algebra R B).X] ≫ (source R B ≫ diagonal R B).hom = _
    exact IsMonHom.mul_hom (source R B ≫ diagonal R B).hom
  · rw [Category.assoc, connectionHom_target, Category.comp_id, Category.assoc,
      IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom, connectionHom_target,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      connectionHom_primitive, connectionCochain_mul, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain, connectionHom_product_comparison]

/-- 四辺を保持する connection は単位と積を保つ実 dg 代数射。 -/
def connection : algebra R B ⟶ algebra R (algebra R B) :=
  Mon.Hom.mk' (connectionHom R B) (connectionHom_one R B) (connectionHom_mul R B)

lemma connection_source : connection R B ≫ source R (algebra R B) =
    source R B ≫ diagonal R B := by
  apply Mon.Hom.ext
  exact connectionHom_source R B

lemma connection_target : connection R B ≫ target R (algebra R B) = 𝟙 (algebra R B) := by
  apply Mon.Hom.ext
  exact connectionHom_target R B

lemma connection_innerSource : connection R B ≫ map R (source R B) =
    source R B ≫ diagonal R B := by
  apply Mon.Hom.ext
  exact connectionHom_innerSource R B

lemma connection_innerTarget : connection R B ≫ map R (target R B) = 𝟙 (algebra R B) := by
  apply Mon.Hom.ext
  exact connectionHom_innerTarget R B

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
