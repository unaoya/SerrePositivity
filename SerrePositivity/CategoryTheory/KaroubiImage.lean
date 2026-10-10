module

public import SerrePositivity.CategoryTheory.KaroubiLinear
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Karoubi 延長の値と冪等元の像

アーベル圏に値をもつ関手を Karoubi 包絡に延長すると、形式的直和因子の値は
対応する冪等元の像に同型になる。射影の持ち上げの可否に依存しない記述である。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents

variable {A : Type*} [Category* A] [Abelian A]

/-- 分裂する冪等元の像は、その直和因子に同型である。 -/
noncomputable def splitIdempotentImageIso {X Y : A} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) : X ≅ Abelian.image (r ≫ i) where
  hom := i ≫ Abelian.factorThruImage (r ≫ i)
  inv := Abelian.image.ι (r ≫ i) ≫ r
  hom_inv_id := by simp only [Category.assoc]; simp [← Category.assoc, h]
  inv_hom_id := by
    apply (cancel_mono (Abelian.image.ι (r ≫ i))).mp
    simp only [Category.assoc, Abelian.image.fac, Category.id_comp]
    have hp : Abelian.image.ι (r ≫ i) ≫ r ≫ i = Abelian.image.ι (r ≫ i) := by
      apply (cancel_epi (Abelian.factorThruImage (r ≫ i))).mp
      simp only [← Category.assoc, Abelian.image.fac]
      simp only [Category.assoc, reassoc_of% h]
    simpa only [Category.assoc, reassoc_of% h, Category.id_comp] using hp

variable {C : Type*} [Category* C] (F : C ⥤ A)

/-- 関手の Karoubi 延長の値は、元の冪等元を送った射の像に同型である。 -/
noncomputable def karoubiExtensionImageIso (P : Karoubi C) :
    ((functorExtension C A).obj F).obj P ≅ Abelian.image (F.map P.p) := by
  let E := (functorExtension C A).obj F
  let e := (karoubiExtensionToCompleteFactors F).app P.X
  let i := E.map P.decompId_i ≫ e.hom
  let r := e.inv ≫ E.map P.decompId_p
  have h : i ≫ r = 𝟙 (E.obj P) := by
    dsimp only [i, r]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← E.map_comp,
      ← P.decompId, CategoryTheory.Functor.map_id]
  have hp : r ≫ i = F.map P.p := by
    dsimp only [i, r]
    rw [Category.assoc, ← Category.assoc (E.map P.decompId_p), ← E.map_comp, ← P.decomp_p]
    have he := (karoubiExtensionToCompleteFactors F).hom.naturality P.p
    change E.map ((toKaroubi C).map P.p) ≫ e.hom = e.hom ≫ F.map P.p at he
    rw [he, Iso.inv_hom_id_assoc]
  have hi := splitIdempotentImageIso i r h
  rw [hp] at hi
  exact hi

end SerrePositivity
