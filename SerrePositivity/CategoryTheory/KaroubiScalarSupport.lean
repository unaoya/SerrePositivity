module

public import SerrePositivity.CategoryTheory.KaroubiLinear
public import SerrePositivity.CategoryTheory.KaroubiFullyFaithful
public import SerrePositivity.CategoryTheory.ScalarSupportLocalization

/-!
# 冪等完備化後の支持対象の直和因子表示

形式的直和因子への Hom の完全性を、元の三角圏の完全性から取り出す。
これにより Karoubi 包絡の三角構造を先に構成しなくても、支持対象を
商の前で台をもつ対象の像の直和因子として表示できる。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Pretriangulated
open CategoryTheory.Limits

variable {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- 完全三角形に対する Hom の完全性は、値域を形式的直和因子にしても成立する。 -/
lemma karoubi_yoneda_exact₂ (T : Triangle D) (hT : T ∈ distTriang D)
    (P : Karoubi D) (f : (toKaroubi D).obj T.obj₂ ⟶ P)
    (hf : (toKaroubi D).map T.mor₁ ≫ f = 0) :
    ∃ g : (toKaroubi D).obj T.obj₃ ⟶ P, f = (toKaroubi D).map T.mor₂ ≫ g := by
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT f.f (congrArg Karoubi.Hom.f hf)
  refine ⟨⟨g ≫ P.p, by simp⟩, ?_⟩
  apply Karoubi.hom_ext
  change f.f = T.mor₂ ≫ (g ≫ P.p)
  rw [← Category.assoc, ← hg, Karoubi.comp_p]

variable {R : Type*} [CommRing R] [Linear R D]
  {C : Type*} [Category* C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

/-- 像の形式的直和因子が台をもてば、元の圏で台をもつ対象の像の直和因子にできる。 -/
theorem karoubi_scalarSupported_retract :
    ∀ {n : ℕ} (z : Fin n → R) (P : Karoubi D) (X : C),
      Retract P ((toKaroubi D).obj (F.obj X)) → scalarSupported z P →
      ∃ Z : C, scalarSupported z Z ∧
        Nonempty (Retract P ((toKaroubi D).obj (F.obj Z))) := by
  intro n
  induction n with
  | zero =>
      intro z P X r _
      exact ⟨X, ⟨1, by omega, fun j ↦ j.elim0⟩, ⟨r⟩⟩
  | succ n ih =>
      intro z P X r hP
      obtain ⟨v, hv, hP⟩ := hP
      obtain ⟨Z, hZ, ⟨r⟩⟩ := ih (Fin.init z) P X r ⟨v, hv, fun j ↦ hP j.castSucc⟩
      let c := z (Fin.last n) ^ v
      obtain ⟨W, g, h, hT⟩ := distinguished_cocone_triangle (c • 𝟙 Z)
      let T := Triangle.mk (c • 𝟙 Z) g h
      have hinit : scalarSupported (Fin.init z) W :=
        scalarSupported_triangle (Fin.init z) T hT hZ hZ
      have hc : (c * c) • 𝟙 W = 0 :=
        smul_mul_self_id_eq_zero T hT c
          (comp_distTriang_mor_zero₁₂ T hT) (comp_distTriang_mor_zero₃₁ T hT)
      have hr : (toKaroubi D).map (F.mapTriangle.obj T).mor₁ ≫ r.r = 0 := by
        apply Karoubi.hom_ext
        change F.map (c • 𝟙 Z) ≫ r.r.f = 0
        have hp : c • P.p = 0 := congrArg Karoubi.Hom.f (hP (Fin.last n))
        calc
          _ = r.r.f ≫ (c • P.p) := by simp
          _ = 0 := by rw [hp, comp_zero]
      obtain ⟨b, hb⟩ := karoubi_yoneda_exact₂ (F.mapTriangle.obj T)
        (F.map_distinguished T hT) P r.r hr
      refine ⟨W, scalarSupported_fin_succ z W hinit (v + v) (by omega) ?_,
        ⟨⟨r.i ≫ (toKaroubi D).map (F.map g), b, ?_⟩⟩⟩
      · simpa only [pow_add] using hc
      · change (r.i ≫ (toKaroubi D).map (F.mapTriangle.obj T).mor₂) ≫ b = _
        rw [Category.assoc, ← hb, r.retract]

/-- 本質的全射な三角関手に対して、冪等完備化後の全支持対象を表示する。 -/
theorem karoubi_scalarSupported_retract_image [F.EssSurj] {n : ℕ} (z : Fin n → R)
    (P : Karoubi D) (hP : scalarSupported z P) :
    ∃ Z : C, scalarSupported z Z ∧
      Nonempty (Retract P ((toKaroubi D).obj (F.obj Z))) := by
  let e := F.objObjPreimageIso P.X
  exact karoubi_scalarSupported_retract F z P (F.objPreimage P.X)
    ((karoubiRetract P).trans (Retract.ofIso ((toKaroubi D).mapIso e.symm))) hP

end SerrePositivity
