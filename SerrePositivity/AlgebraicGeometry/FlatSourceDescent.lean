module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
概要：始域の平坦全射に沿って射の平坦性を降ろす。
方針：各点の上の点を選び、茎の平坦な局所準同型の忠実平坦性を使う。
規約：被覆する射と合成の平坦性を仮定する。
使われ方：étale 局所で得られた純変換の平坦性を基底側に降ろす。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

private theorem flat_of_faithfullyFlat_tower
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  apply Module.Flat.iff_lTensor_preserves_injective_linearMap.mpr
  intro M N _ _ _ _ f hf
  change Function.Injective (f.baseChange S)
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T (f.baseChange S)).mp
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N
  have h : ⇑(f.baseChange T) ∘ ⇑eM = ⇑eN ∘ ⇑((f.baseChange S).baseChange T) :=
    congrArg DFunLike.coe
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R S T (M := T) f)
  change Function.Injective ((f.baseChange S).baseChange T)
  apply Function.Injective.of_comp (f := eN)
  rw [← h]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp eM.injective

/--
概要：射の始域を平坦全射で覆った合成が平坦なら、元の射も平坦。
方針：茎では平坦な局所準同型が忠実平坦なので、テンソル積による単射性の保存を反映する。
規約：被覆は一つの平坦全射で表す。
使われ方：étale 基底変換後の純変換から、元の純変換の平坦性を得る。
-/
theorem flat_of_flat_surjective_source
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X)
    [Flat g] [Surjective g] [Flat (g ≫ f)] : Flat f := by
  apply Flat.of_stalkMap
  intro x
  obtain ⟨z, rfl⟩ := g.surjective x
  let A : Type u := Y.presheaf.stalk (f (g z))
  let B : Type u := X.presheaf.stalk (g z)
  let C : Type u := Z.presheaf.stalk z
  let φ : A →+* B := (f.stalkMap (g z)).hom
  let ψ : B →+* C := (g.stalkMap z).hom
  let : IsLocalHom ψ := inferInstanceAs (IsLocalHom (g.stalkMap z).hom)
  have hψ : ψ.Flat := Flat.stalkMap g z
  have hcomp : (ψ.comp φ).Flat := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact Flat.stalkMap (g ≫ f) z
  let : Algebra A B := φ.toAlgebra
  let : Algebra B C := ψ.toAlgebra
  let : Algebra A C := (ψ.comp φ).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat B C := hψ
  let : Module.Flat A C := hcomp
  let : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_faithfullyFlat_tower (R := A) (S := B) (T := C)

end SerrePositivity.AlgebraicGeometry
