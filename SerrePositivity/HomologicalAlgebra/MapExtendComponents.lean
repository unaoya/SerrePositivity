module
public import SerrePositivity.HomologicalAlgebra.MapExtendComplex
import all Mathlib.Algebra.Homology.Embedding.Extend

/-!
概要：関手と零延長の自然同型の、元の次数での指定成分の公式。
方針：零延長の指定同型を用い、元の関手による成分の像と厳密に照合する。
規約：複体の同型の存在だけでなく、元の射影との比較に使う等式を保持する。
使われ方：HA 1.2.4、G10 の離散入力の標準射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [HasZeroObject D]
variable (F : C ⥤ D) [F.Additive]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- 元の次数における比較射は、零延長の指定同型と可換。 -/
theorem mapExtendIso_hom_f (e : c.Embedding c') (K : HomologicalComplex C c)
    {i : ι} {j : ι'} (h : e.f i = j) :
    (mapExtendIso F e K).hom.f j ≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
        F.map ((K.extendXIso e h).hom) := by
  classical
  have hi : ∃ a, e.f a = j := ⟨i, h⟩
  have hei : hi.choose = i := e.injective_f (hi.choose_spec.trans h.symm)
  subst i
  simp [mapExtendIso, SerrePositivity.mapExtendIso, SerrePositivity.mapExtendXIso, hi]


/-- 逆比較も同じ指定同型で元の次数へ戻る。 -/
theorem mapExtendIso_inv_f (e : c.Embedding c') (K : HomologicalComplex C c)
    {i : ι} {j : ι'} (h : e.f i = j) :
    (mapExtendIso F e K).inv.f j =
      (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom ≫
        F.map ((K.extendXIso e h).inv) := by
  have hh := mapExtendIso_hom_f F e K h
  apply (cancel_epi ((mapExtendIso F e K).hom.f j)).mp
  rw [← Category.assoc, hh, ← F.map_comp]
  simp
  exact congrArg (fun f => f.f j) (mapExtendIso F e K).hom_inv_id

end SerrePositivity.HomologicalAlgebra
