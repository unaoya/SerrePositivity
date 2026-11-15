module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
概要：非有界複体の線形 Hom 関手の加法性。
方針：既存の homFunctor の後合成を成分で計算する。
規約：既存の関手を変更せず、加法的関手としての構造だけを供給する。
使われ方：HA 1.2.4、交代余面複体と Hom 関手の交換。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Preadditive CochainComplex HomComplex
namespace SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 固定された非有界複体からの Hom は加法的。 -/
instance homFunctor_additive (P : Complex A) : (homFunctor P).Additive where
  map_add {X Y} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change z.comp (Cochain.ofHom (f + g)) (add_zero n) =
      z.comp (Cochain.ofHom f) (add_zero n) + z.comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_add, Cochain.comp_add]

end SerrePositivity.DifferentialGraded
