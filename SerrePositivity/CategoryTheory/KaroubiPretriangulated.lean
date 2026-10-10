module

public import SerrePositivity.CategoryTheory.KaroubiShift
public import SerrePositivity.CategoryTheory.KaroubiFullyFaithful
public import SerrePositivity.CategoryTheory.TriangleIdempotentCompletion
public import Mathlib.CategoryTheory.Idempotents.Biproducts

/-! # Karoubi 包絡の完全三角形

元の完全三角形の像の retract を完全三角形とする。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated
open scoped ZeroObject

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 元の完全三角形の像の直和因子として得られる三角形。 -/
def karoubiDistinguished (T : Triangle (Karoubi C)) : Prop :=
  ∃ U : Triangle C, U ∈ distTriang C ∧
    Nonempty (Retract T ((toKaroubi C).mapTriangle.obj U))

lemma karoubiDistinguished_image (U : Triangle C) (hU : U ∈ distTriang C) :
    karoubiDistinguished ((toKaroubi C).mapTriangle.obj U) :=
  ⟨U, hU, ⟨Retract.refl _⟩⟩

lemma karoubiDistinguished_retract {T U : Triangle (Karoubi C)} (hU : karoubiDistinguished U)
    (r : Retract T U) : karoubiDistinguished T := by
  obtain ⟨V, hV, ⟨s⟩⟩ := hU
  exact ⟨V, hV, ⟨r.trans s⟩⟩

lemma karoubiDistinguished_iso {T U : Triangle (Karoubi C)} (hU : karoubiDistinguished U)
    (e : T ≅ U) : karoubiDistinguished T :=
  karoubiDistinguished_retract hU (Retract.ofIso e)

lemma karoubiDistinguished_rotate {T : Triangle (Karoubi C)}
    (hT : karoubiDistinguished T) : karoubiDistinguished T.rotate := by
  obtain ⟨U, hU, ⟨r⟩⟩ := hT
  exact ⟨U.rotate, rot_of_distTriang U hU,
    ⟨(r.map (rotate (Karoubi C))).trans
      (Retract.ofIso (((toKaroubi C).mapTriangleRotateIso).app U))⟩⟩

lemma karoubiDistinguished_invRotate {T : Triangle (Karoubi C)}
    (hT : karoubiDistinguished T) : karoubiDistinguished T.invRotate := by
  obtain ⟨U, hU, ⟨r⟩⟩ := hT
  exact ⟨U.invRotate, inv_rot_of_distTriang U hU,
    ⟨(r.map (invRotate (Karoubi C))).trans
      (Retract.ofIso (((toKaroubi C).mapTriangleInvRotateIso).app U))⟩⟩

/-- 二つの直和因子の間の可換な正方形を三角形の射に延長する。 -/
lemma karoubiDistinguished_complete {T U : Triangle (Karoubi C)}
    (hT : karoubiDistinguished T) (hU : karoubiDistinguished U)
    (a : T.obj₁ ⟶ U.obj₁) (b : T.obj₂ ⟶ U.obj₂)
    (hab : T.mor₁ ≫ b = a ≫ U.mor₁) :
    ∃ c : T.obj₃ ⟶ U.obj₃, T.mor₂ ≫ c = b ≫ U.mor₂ ∧
      T.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ U.mor₃ := by
  obtain ⟨T', hT', ⟨r⟩⟩ := hT
  obtain ⟨U', hU', ⟨s⟩⟩ := hU
  let F := toKaroubi C
  let a' := F.preimage (r.r.hom₁ ≫ a ≫ s.i.hom₁)
  let b' := F.preimage (r.r.hom₂ ≫ b ≫ s.i.hom₂)
  have hab' : T'.mor₁ ≫ b' = a' ≫ U'.mor₁ := by
    apply F.map_injective
    simp only [Functor.map_comp, a', b', Functor.map_preimage]
    change (F.mapTriangle.obj T').mor₁ ≫ _ = _ ≫ (F.mapTriangle.obj U').mor₁
    simp only [Category.assoc]
    rw [r.r.comm₁_assoc, ← Category.assoc T.mor₁, hab, Category.assoc,
      s.i.comm₁]
  obtain ⟨c', hc'₂, hc'₃⟩ :=
    complete_distinguished_triangle_morphism T' U' hT' hU' a' b' hab'
  let f : T' ⟶ U' := ⟨a', b', c', hab', hc'₂, hc'₃⟩
  let g := r.i ≫ F.mapTriangle.map f ≫ s.r
  have hg₁ : g.hom₁ = a := by
    change r.i.hom₁ ≫ F.map a' ≫ s.r.hom₁ = a
    simp only [a', Functor.map_preimage]
    have hr := congrArg TriangleMorphism.hom₁ r.retract
    have hs := congrArg TriangleMorphism.hom₁ s.retract
    change r.i.hom₁ ≫ r.r.hom₁ = 𝟙 _ at hr
    change s.i.hom₁ ≫ s.r.hom₁ = 𝟙 _ at hs
    simp only [Category.assoc, hs, Category.comp_id]
    rw [← Category.assoc, hr, Category.id_comp]
  have hg₂ : g.hom₂ = b := by
    change r.i.hom₂ ≫ F.map b' ≫ s.r.hom₂ = b
    simp only [b', Functor.map_preimage]
    have hr := congrArg TriangleMorphism.hom₂ r.retract
    have hs := congrArg TriangleMorphism.hom₂ s.retract
    change r.i.hom₂ ≫ r.r.hom₂ = 𝟙 _ at hr
    change s.i.hom₂ ≫ s.r.hom₂ = 𝟙 _ at hs
    simp only [Category.assoc, hs, Category.comp_id]
    rw [← Category.assoc, hr, Category.id_comp]
  exact ⟨g.hom₃, hg₂ ▸ g.comm₂, hg₁ ▸ g.comm₃⟩

lemma karoubiDistinguished_contractible (P : Karoubi C) :
    karoubiDistinguished (contractibleTriangle P) := by
  have hz := (toKaroubi C).map_isZero (isZero_zero C)
  let e : contractibleTriangle ((toKaroubi C).obj P.X) ≅
      (toKaroubi C).mapTriangle.obj (contractibleTriangle P.X) :=
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((isZero_zero (Karoubi C)).iso hz)
      (by
        dsimp only [Triangle.mk, contractibleTriangle, Functor.mapTriangle, Iso.refl]
        simp only [Category.id_comp, Category.comp_id]
        exact ((toKaroubi C).map_id P.X).symm)
      (by
        dsimp only [Triangle.mk, contractibleTriangle, Functor.mapTriangle, Iso.refl]
        simp only [Functor.map_zero, zero_comp, comp_zero])
      (by
        dsimp only [Triangle.mk, contractibleTriangle, Functor.mapTriangle, Iso.refl]
        simp only [Functor.map_zero, zero_comp, comp_zero])
  exact karoubiDistinguished_retract
    (karoubiDistinguished_iso (karoubiDistinguished_image _ (contractible_distinguished P.X)) e)
    ((karoubiRetract P).map (contractibleTriangleFunctor (Karoubi C)))

/-- 射の錐の上で冪等元を延長し、その像を Karoubi 包絡の錐とする。 -/
lemma karoubiDistinguished_cocone {P Q : Karoubi C} (f : P ⟶ Q) :
    ∃ (R : Karoubi C) (g : Q ⟶ R) (h : R ⟶ P⟦(1 : ℤ)⟧),
      karoubiDistinguished (Triangle.mk f g h) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f.f
  obtain ⟨r, hr, hg, hh⟩ := complete_triangle_idempotent (Triangle.mk f.f g h) hT
    P.p Q.p P.idem Q.idem (by simp)
  change g ≫ r = Q.p ≫ g at hg
  change h ≫ P.p⟦(1 : ℤ)⟧' = r ≫ h at hh
  let R : Karoubi C := ⟨Z, r, hr⟩
  let g' : Q ⟶ R := ⟨Q.p ≫ g, by
    change Q.p ≫ (Q.p ≫ g) ≫ r = Q.p ≫ g
    simp only [Category.assoc, hg]
    simp only [← Category.assoc, Q.idem]⟩
  let h' : R ⟶ P⟦(1 : ℤ)⟧ := ⟨r ≫ h, by
    change r ≫ (r ≫ h) ≫ P.p⟦(1 : ℤ)⟧' = r ≫ h
    simp only [Category.assoc, hh]
    simp only [← Category.assoc, hr]⟩
  refine ⟨R, g', h', Triangle.mk f.f g h, hT, ⟨?_⟩⟩
  let i : Triangle.mk f g' h' ⟶ (toKaroubi C).mapTriangle.obj (Triangle.mk f.f g h) :=
    { hom₁ := P.decompId_i
      hom₂ := Q.decompId_i
      hom₃ := R.decompId_i
      comm₁ := by ext; simp
      comm₂ := by
        ext
        change (Q.p ≫ g) ≫ r = Q.p ≫ g
        rw [Category.assoc, hg, ← Category.assoc, Q.idem]
      comm₃ := by
        ext
        change (r ≫ h) ≫ P.p⟦(1 : ℤ)⟧' = r ≫ h ≫ 𝟙 _
        rw [Category.comp_id, Category.assoc, hh, ← Category.assoc, hr] }
  let p : (toKaroubi C).mapTriangle.obj (Triangle.mk f.f g h) ⟶ Triangle.mk f g' h' :=
    { hom₁ := P.decompId_p
      hom₂ := Q.decompId_p
      hom₃ := R.decompId_p
      comm₁ := by ext; simp
      comm₂ := by
        ext
        change g ≫ r = Q.p ≫ Q.p ≫ g
        rw [← Category.assoc, Q.idem, hg]
      comm₃ := by
        ext
        change (h ≫ 𝟙 _) ≫ P.p⟦(1 : ℤ)⟧' = r ≫ r ≫ h
        rw [Category.comp_id, hh, ← Category.assoc, hr] }
  exact ⟨i, p, by
    apply TriangleMorphism.ext
    · exact P.decompId.symm
    · exact Q.decompId.symm
    · exact R.decompId.symm⟩

/-- Karoubi 包絡上の標準的な前三角構造。 -/
noncomputable instance karoubiPretriangulated : Pretriangulated (Karoubi C) where
  distinguishedTriangles := {T | karoubiDistinguished T}
  isomorphic_distinguished _ hT _ e := karoubiDistinguished_iso hT e
  contractible_distinguished := karoubiDistinguished_contractible
  distinguished_cocone_triangle := karoubiDistinguished_cocone
  rotate_distinguished_triangle T :=
    ⟨karoubiDistinguished_rotate, fun h ↦
      karoubiDistinguished_iso (karoubiDistinguished_invRotate h) (rotCompInvRot.app T)⟩
  complete_distinguished_triangle_morphism _ _ := karoubiDistinguished_complete

instance toKaroubi_isTriangulated : (toKaroubi C).IsTriangulated where
  map_distinguished := karoubiDistinguished_image

end SerrePositivity
