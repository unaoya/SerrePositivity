module

public import SerrePositivity.CategoryTheory.Karoubi.Basic
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent
public import Mathlib.CategoryTheory.Idempotents.Biproducts
public import SerrePositivity.CategoryTheory.Triangulated.Padding
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.CategoryTheory.Abelian.ShortComplex
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # 三角圏の Karoubi 完備化（Balmer–Schlichting）

## 概要

三角圏 C の Karoubi 包絡が三角圏になること（Balmer–Schlichting, Theorem 1.12）：元の完全三角形の像の retract を完全三角形とし、八面体公理を示す。三角関手・ホモロジー関手の Karoubi 包絡への延長も与える。

## 方針

完全三角形は「元の完全三角形の像の retract」と定義する。八面体は、自明な三角形を加えた八面体のブロック形（`Triangulated/Padding`）から retract で降ろす。

## 規約

`Karoubi/Basic` のシフトを使う。延長の一意性は扱わない。

## 使われ方

Verdier 商と完備化の交換（`Triangulated/VerdierKaroubi`）、t 構造の冪等完備性、Asymptotic の完備化した階数の商、DifferentialGraded の比較。
-/

@[expose] public noncomputable section

section KaroubiPretriangulatedPart

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

end KaroubiPretriangulatedPart

section KaroubiTriangulatedPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

/-- 標準的な前三角構造を備えた Karoubi 包絡は八面体公理を満たす。 -/
instance karoubiIsTriangulated : IsTriangulated (Karoubi C) where
  octahedron_axiom {X Y Z U V W u v w} comm {a b} h₁ {c d} h₂ {e f} h₃ := by
    let A := X.complement
    let B := Y.complement
    let D := Z.complement
    have hX : (toKaroubi C).essImage (X ⊞ A) := ⟨X.X, ⟨X.decomposition.symm⟩⟩
    have hY : (toKaroubi C).essImage (Y ⊞ B) := ⟨Y.X, ⟨Y.decomposition.symm⟩⟩
    have hZ : (toKaroubi C).essImage (Z ⊞ D) := ⟨Z.X, ⟨Z.decomposition.symm⟩⟩
    obtain ⟨H⟩ := nonempty_octahedron_of_essImage (toKaroubi C)
      (paddedTriangle_comp comm A B D)
      (paddedTriangle_distinguished _ h₁ A B)
      (paddedTriangle_distinguished _ h₂ B D)
      (paddedTriangle_distinguished _ h₃ A D) hX hY hZ
    exact ⟨octahedronOfPadding comm h₁ h₂ h₃ A B D H
      (fun _ _ h r ↦ karoubiDistinguished_retract h r)⟩

end SerrePositivity

end KaroubiTriangulatedPart

section KaroubiTriangulatedFunctorPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]

noncomputable instance karoubiExtension_commShift :
    ((functorExtension₂ C D).obj F).CommShift ℤ :=
  commShiftOfPrecomp (toKaroubi C) ((functorExtension₂ C D).obj F) (F ⋙ toKaroubi D)
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)

instance karoubiExtensionFactors_commShift :
    NatTrans.CommShift (show toKaroubi C ⋙ (functorExtension₂ C D).obj F ⟶ F ⋙ toKaroubi D
      from ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F).hom) ℤ :=
  commShiftOfPrecomp_compatibility (toKaroubi C) ((functorExtension₂ C D).obj F)
    (F ⋙ toKaroubi D) ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]

/-- 完全三角形の retract を用いた標準構造に関して延長関手は三角関手。 -/
instance karoubiExtension_isTriangulated : ((functorExtension₂ C D).obj F).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨U, hU, ⟨r⟩⟩ := hT
    let G := (functorExtension₂ C D).obj F
    let eF : toKaroubi C ⋙ G ≅ F ⋙ toKaroubi D :=
      (functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F
    have : NatTrans.CommShift eF.hom ℤ := karoubiExtensionFactors_commShift F
    let e := ((toKaroubi C).mapTriangleCompIso G).symm.app U ≪≫
      (Functor.mapTriangleIso eF).app U ≪≫
      (F.mapTriangleCompIso (toKaroubi D)).app U
    exact karoubiDistinguished_retract
      (karoubiDistinguished_iso (karoubiDistinguished_image _ (F.map_distinguished U hU)) e)
      (r.map G.mapTriangle)

end SerrePositivity

end KaroubiTriangulatedFunctorPart

section KaroubiExtensionOnePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ Karoubi D) [F.CommShift ℤ]

noncomputable instance karoubiExtensionOne_commShift :
    ((functorExtension₁ C D).obj F).CommShift ℤ :=
  commShiftOfPrecomp (toKaroubi C) ((functorExtension₁ C D).obj F) F
    ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F)

instance karoubiExtensionOneFactors_commShift :
    NatTrans.CommShift (show toKaroubi C ⋙ (functorExtension₁ C D).obj F ⟶ F from
      ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F).hom) ℤ :=
  commShiftOfPrecomp_compatibility (toKaroubi C) ((functorExtension₁ C D).obj F) F
    ((functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F)

variable [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [F.IsTriangulated]

instance karoubiExtensionOne_isTriangulated : ((functorExtension₁ C D).obj F).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨U, hU, ⟨r⟩⟩ := hT
    let G := (functorExtension₁ C D).obj F
    let eF : toKaroubi C ⋙ G ≅ F :=
      (functorExtension₁CompWhiskeringLeftToKaroubiIso C D).app F
    have : NatTrans.CommShift eF.hom ℤ := karoubiExtensionOneFactors_commShift F
    let e := ((toKaroubi C).mapTriangleCompIso G).symm.app U ≪≫
      (Functor.mapTriangleIso eF).app U
    exact karoubiDistinguished_retract
      (karoubiDistinguished_iso (F.map_distinguished U hU) e) (r.map G.mapTriangle)

end SerrePositivity

end KaroubiExtensionOnePart

section KaroubiHomologicalPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents
open CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 三角形の retract は、最初の三項からなる短複体の retract を与える。 -/
def shortComplexOfDistTriangleRetract {T U : Triangle C}
    (hT : T ∈ distTriang C) (hU : U ∈ distTriang C) (r : Retract T U) :
    Retract (shortComplexOfDistTriangle T hT) (shortComplexOfDistTriangle U hU) where
  i := ⟨r.i.hom₁, r.i.hom₂, r.i.hom₃, r.i.comm₁.symm, r.i.comm₂.symm⟩
  r := ⟨r.r.hom₁, r.r.hom₂, r.r.hom₃, r.r.comm₁.symm, r.r.comm₂.symm⟩
  retract := by
    apply ShortComplex.Hom.ext
    · exact congrArg TriangleMorphism.hom₁ r.retract
    · exact congrArg TriangleMorphism.hom₂ r.retract
    · exact congrArg TriangleMorphism.hom₃ r.retract

variable {A : Type*} [Category* A] [Abelian A]

/-- 元の圏でホモロジー的なら、Karoubi 包絡上でもホモロジー的である。 -/
theorem karoubi_isHomological_of_restriction (F : Karoubi C ⥤ A)
    [F.PreservesZeroMorphisms] [(toKaroubi C ⋙ F).IsHomological] : F.IsHomological where
  exact T hT := by
    have hd := hT
    obtain ⟨U, hU, ⟨r⟩⟩ := hd
    have hU' := (toKaroubi C).map_distinguished U hU
    apply shortComplex_exact_of_retract
      ((shortComplexOfDistTriangleRetract hT hU' r).map F.mapShortComplex)
    exact (toKaroubi C ⋙ F).map_distinguished_exact U hU

/-- アーベル圏を値域とするホモロジー関手の標準延長はホモロジー関手。 -/
instance karoubiExtensionToComplete_isHomological (F : C ⥤ A) [F.IsHomological] :
    ((functorExtension C A).obj F).IsHomological := by
  let e := karoubiExtensionToCompleteFactors F
  have : (toKaroubi C ⋙ (functorExtension C A).obj F).IsHomological :=
    Functor.IsHomological.of_iso e.symm
  exact karoubi_isHomological_of_restriction _

end SerrePositivity

end KaroubiHomologicalPart
