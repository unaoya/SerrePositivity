module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovExtensionConeMap

/-!
概要：Postnikov の微分変更代数の実射は、元の代数射の恒等・合成を厳密に保つ。
方針：次数ごとの直和射と、既存の切断・層・shift の関手則を使う。
規約：cell lift の選択を使わない。使われ方：元の拡大の塔と class の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C D : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n)

lemma postnikovPerturbedMap_id : postnikovPerturbedMap R (𝟙 B) n hn = 𝟙 _ := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  rw [postnikovPerturbedMap_f, postnikovLayerMap_id]
  have hb : (postnikovMap R (𝟙 B) (n + 1)).hom = 𝟙 _ :=
    (postnikovComplex R (n + 1)).map_id B
  have hs := (CategoryTheory.shiftFunctor (Complex R) (1 : ℤ)).map_id
    (postnikovLayer R B n)
  have hid : biprod.map (𝟙 (postnikov R B (n + 1)).X)
      (𝟙 ((postnikovLayer R B n)⟦(1 : ℤ)⟧)) = 𝟙 _ := by
    apply biprod.hom_ext <;> simp
  rw [hb]
  exact (congrArg (fun t => (biprod.map (𝟙 (postnikov R B (n + 1)).X) t).f p) hs).trans
    ((congrArg (fun t => t.f p) hid).trans (by rfl))

lemma postnikovPerturbedMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    postnikovPerturbedMap R (f ≫ g) n hn =
      postnikovPerturbedMap R f n hn ≫ postnikovPerturbedMap R g n hn := by
  apply Mon.Hom.ext
  apply HomologicalComplex.hom_ext
  intro p
  change (postnikovPerturbedMap R (f ≫ g) n hn).hom.f p =
    (postnikovPerturbedMap R f n hn).hom.f p ≫ (postnikovPerturbedMap R g n hn).hom.f p
  rw [postnikovPerturbedMap_f, postnikovPerturbedMap_f, postnikovPerturbedMap_f]
  have hb : (postnikovMap R (f ≫ g) (n + 1)).hom =
      (postnikovMap R f (n + 1)).hom ≫ (postnikovMap R g (n + 1)).hom :=
    (postnikovComplex R (n + 1)).map_comp f g
  have hs := (CategoryTheory.shiftFunctor (Complex R) (1 : ℤ)).map_comp
    (postnikovLayerMap R f n) (postnikovLayerMap R g n)
  rw [hb, postnikovLayerMap_comp]
  have he : biprod.map ((postnikovMap R f (n + 1)).hom ≫ (postnikovMap R g (n + 1)).hom)
      (((postnikovLayerMap R f n) ≫ (postnikovLayerMap R g n))⟦(1 : ℤ)⟧') =
      biprod.map (postnikovMap R f (n + 1)).hom ((postnikovLayerMap R f n)⟦(1 : ℤ)⟧') ≫
        biprod.map (postnikovMap R g (n + 1)).hom ((postnikovLayerMap R g n)⟦(1 : ℤ)⟧') := by
    rw [hs]
    apply biprod.hom_ext <;> simp [Category.assoc]
  exact congrArg (fun t => t.f p) he

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
