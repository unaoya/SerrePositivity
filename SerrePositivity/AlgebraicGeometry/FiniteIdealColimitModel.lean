module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
概要：filtered な環の colimit 上の有限生成イデアルを、一つの有限段へ降ろす。
方針：有限生成元を underlying type の colimit から選び、共通の後段へ移して span を取る。
規約：Stacks 0B8W (3) のアフィン部分。実際の cocone の IsColimit を使う。
使われ方：C03、G1 の整拡大後の閉包絡と G2 の模型の降下。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

/-- filtered な環の colimit の有限生成イデアルは、有限段の有限生成イデアルの像。 -/
theorem exists_fg_ideal_model_of_isColimit
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u})
    (c : Cocone F) (hc : IsColimit c) (I : Ideal c.pt) (hI : I.FG) :
    ∃ (j : J) (I₀ : Ideal (F.obj j)), I₀.FG ∧ I₀.map (c.ι.app j).hom = I := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hrep (x : s) : ∃ (j : J) (y : F.obj j), c.ι.app j y = x.1 :=
    Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget CommRingCat) hc) x.1
  choose j y hy using hrep
  obtain ⟨k, hk⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let f (x : s) : j x ⟶ k :=
    (hk (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)).some
  let z (x : s) : F.obj k := F.map (f x) (y x)
  have hz (x : s) : c.ι.app k (z x) = x.1 := by
    calc
      _ = c.ι.app (j x) (y x) :=
        congrArg (fun q : F.obj (j x) ⟶ c.pt ↦ q (y x)) (c.w (f x))
      _ = x.1 := hy x
  let t : Finset (F.obj k) := Finset.univ.image z
  have himage : (c.ι.app k).hom '' (t : Set (F.obj k)) = (s : Set c.pt) := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
      rw [hz]
      exact x.2
    · intro hb
      exact ⟨z ⟨b, hb⟩, Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩, hz ⟨b, hb⟩⟩
  refine ⟨k, Ideal.span (t : Set (F.obj k)), ⟨t, rfl⟩, ?_⟩
  rw [Ideal.map_span, himage]
  exact hs

end SerrePositivity.AlgebraicGeometry
