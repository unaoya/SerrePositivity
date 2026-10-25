module
public import SerrePositivity.DifferentialGraded.Complexes.SphereTensorShift
public import SerrePositivity.DifferentialGraded.Complexes.TensorShiftSecondNaturality
/-!
概要：sphere tensor shift 同型の任意の Hom 鎖写像に関する自然性を証明する。
方針：tensor の交換則、左 shift の第二変数自然性、左単位の自然性を合成する。
規約：元の sphere 同型と元の鎖写像をそのまま使う。
使われ方：c′ の自由閉射の係数評価と実延長の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R]

lemma complexSphereTensorShiftIso_naturality (n : ℤ) {K L : Complex R} (g : K ⟶ L) :
    (𝟙 (complexSphere R n) ⊗ₘ g) ≫ (complexSphereTensorShiftIso R n L).hom =
      (complexSphereTensorShiftIso R n K).hom ≫ g⟦-n⟧' := by
  have ht : (𝟙 (complexSphere R n) ⊗ₘ g) ≫
      ((complexSphereUnitShiftIso R n).hom ⊗ₘ 𝟙 L) =
      ((complexSphereUnitShiftIso R n).hom ⊗ₘ 𝟙 K) ≫
        (𝟙 ((𝟙_ (Complex R))⟦-n⟧) ⊗ₘ g) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hu : (𝟙 (𝟙_ (Complex R)) ⊗ₘ g)⟦-n⟧' ≫ ((λ_ L).hom)⟦-n⟧' =
      ((λ_ K).hom)⟦-n⟧' ≫ g⟦-n⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (shiftFunctor (Complex R) (-n)).map (leftUnitor_naturality g)
  simp only [complexSphereTensorShiftIso, Iso.trans_hom, tensorIso_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙 ((𝟙_ (Complex R))⟦-n⟧) ⊗ₘ g),
    tensorShiftLeft_second_naturality R (𝟙_ (Complex R)) g (-n)]
  simp only [Category.assoc]
  rw [hu]

end SerrePositivity.DifferentialGraded
