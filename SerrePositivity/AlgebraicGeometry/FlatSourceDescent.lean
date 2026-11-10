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
概要：平坦な射の族で始域の各点を覆い、それぞれの合成が平坦なら、元の射も平坦。
方針：各点を覆う射の茎の忠実平坦性を使い、平坦性を反映する。
規約：被覆族は点集合上で全射とする。
使われ方：étale 局所中心から狭義変換の平坦性を降下する。
-/
theorem flat_of_flat_source_cover
    {X Y : Scheme.{u}} {ι : Type v} {Z : ι → Scheme.{u}} (f : X ⟶ Y)
    (g : ∀ i, Z i ⟶ X) (hg : ∀ i, Flat (g i))
    (hcover : ∀ x : X, ∃ (i : ι) (z : Z i), g i z = x)
    (hflat : ∀ i, Flat (g i ≫ f)) : Flat f := by
  apply Flat.of_stalkMap
  intro x
  obtain ⟨i, z, rfl⟩ := hcover x
  let g₀ := g i
  let : Flat g₀ := hg i
  let : Flat (g₀ ≫ f) := hflat i
  let A : Type u := Y.presheaf.stalk (f (g₀ z))
  let B : Type u := X.presheaf.stalk (g₀ z)
  let C : Type u := (Z i).presheaf.stalk z
  let φ : A →+* B := (f.stalkMap (g₀ z)).hom
  let ψ : B →+* C := (g₀.stalkMap z).hom
  let : IsLocalHom ψ := inferInstanceAs (IsLocalHom (g₀.stalkMap z).hom)
  have hψ : ψ.Flat := Flat.stalkMap g₀ z
  have hcomp : (ψ.comp φ).Flat := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact Flat.stalkMap (g₀ ≫ f) z
  let : Algebra A B := φ.toAlgebra
  let : Algebra B C := ψ.toAlgebra
  let : Algebra A C := (ψ.comp φ).toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Flat B C := hψ
  let : Module.Flat A C := hcomp
  let : Module.FaithfullyFlat B C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact flat_of_faithfullyFlat_tower (R := A) (S := B) (T := C)

/--
概要：射の始域を平坦全射で覆った合成が平坦なら、元の射も平坦。
方針：茎では平坦な局所準同型が忠実平坦なので、テンソル積による単射性の保存を反映する。
規約：被覆は一つの平坦全射で表す。
使われ方：étale 基底変換後の純変換から、元の純変換の平坦性を得る。
-/
theorem flat_of_flat_surjective_source
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ X)
    [Flat g] [Surjective g] [Flat (g ≫ f)] : Flat f := by
  exact flat_of_flat_source_cover f (fun (_ : Unit) => g) (fun _ => inferInstance)
    (fun x => let ⟨z, hz⟩ := g.surjective x; ⟨(), z, hz⟩) (fun _ => inferInstance)

end SerrePositivity.AlgebraicGeometry
