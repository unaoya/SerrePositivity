module

public import SerrePositivity.DifferentialGraded.Verdier.Scalar
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGraphSquare
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Verdier.Karoubi

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## KaroubiFunctorSquare（旧 SerrePositivity/DifferentialGraded/Verdier/KaroubiFunctorSquare.lean） -/

/-! # tria・Perf 間の比較正方形の Karoubi 延長 -/

@[expose] public section KaroubiFunctorSquare
universe u v w t

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C : Type*} [Category* C] {E : Type*} [Category* E] {T : Type*} [Category* T]
  (F : C ⥤ E) (G : E ⥤ T)

def karoubiFunctorCompositionIso :
    (functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G ≅
      (functorExtension₂ C T).obj (F ⋙ G) := Iso.refl _

/-- 元の正方形を、両経路の Karoubi 延長の正方形へ送る。 -/
def karoubiFunctorSquare {E' : Type*} [Category* E'] {F' : C ⥤ E'} {G' : E' ⥤ T}
    (e : F ⋙ G ≅ F' ⋙ G') :
    (functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G ≅
      (functorExtension₂ C E').obj F' ⋙ (functorExtension₂ E' T).obj G' :=
  karoubiFunctorCompositionIso F G ≪≫ (functorExtension₂ C T).mapIso e ≪≫
    (karoubiFunctorCompositionIso F' G').symm
end General

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- finite cell の Karoubi–Perf 比較は元の tria の包含を延長する。 -/
def triaKaroubiPerfectFactors :
    toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ ≅
      triaToPerfect A D :=
  ((whiskeringRight _ _ _).obj (modulePerfect A D).ι).preimageIso
    (X := toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ)
    (Y := triaToPerfect A D) (finiteCellKaroubiRealization_fac A D Set.univ)

variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (G : TriaCategory A D ⥤ TriaCategory A' E)
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E)

/-- 実際の tria–Perf 正方形から、既存 Karoubi–Perf 同値の自然性を得る。 -/
def triaKaroubiPerfectSquare
    (e : G ⋙ triaToPerfect A' E ≅ triaToPerfect A D ⋙ T) :
    (functorExtension₂ (TriaCategory A D) (TriaCategory A' E)).obj G ⋙
        finiteCellKaroubiToPerfect A' E Set.univ ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ T :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimageIso
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft G (triaKaroubiPerfectFactors A' E) ≪≫ e ≪≫
      isoWhiskerRight (triaKaroubiPerfectFactors A D).symm T ≪≫ Functor.associator _ _ _)

namespace DGQuotient
variable {A D} (φ : A →+* A') (S : Set D)

/-- 係数変更の tria 制限を完備化すると、元の実際の Perf 係数変更となる。 -/
def quotientScalarKaroubiPerfectSquare :
    (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) ⋙
        finiteCellKaroubiToPerfect A' (QuotientObject (ScalarExtension.DGBaseChange φ D) S)
          Set.univ ≅
      finiteCellKaroubiToPerfect A (QuotientObject D S) Set.univ ⋙
        quotientScalarPerfectFunctor φ D S :=
  triaKaroubiPerfectSquare A (QuotientObject D S) _ _ _
    (quotientScalarTriaPerfectSquare φ S)
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end KaroubiFunctorSquare

/-! ## KaroubiSquareShift（旧 SerrePositivity/DifferentialGraded/Verdier/KaroubiSquareShift.lean） -/

/-! # Karoubi–Perf 自然性正方形の比較同型の shift 整合性 -/

@[expose] public section KaroubiSquareShift
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance triaKaroubiPerfectFactorsCommShift :
    NatTrans.CommShift (triaKaroubiPerfectFactors A D).hom ℤ := by
  have he : whiskerRight (triaKaroubiPerfectFactors A D).hom (modulePerfectOver A D Set.univ).ι =
      (finiteCellKaroubiRealization_fac A D Set.univ).hom :=
    ((whiskeringRight _ _ _).obj (modulePerfectOver A D Set.univ).ι).map_preimage _
  let β : (toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ) ⋙
        (modulePerfectOver A D Set.univ).ι ≅
      triaToPerfect A D ⋙ (modulePerfectOver A D Set.univ).ι :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (finiteCellKaroubiToPerfectCompInclusion A D Set.univ) ≪≫
      finiteCellKaroubiRealization_fac A D Set.univ ≪≫
      ((modulePerfectOver A D Set.univ).liftCompιIso (triaInclusion A D) _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by dsimp [β]; infer_instance
  have he' : whiskerRight (triaKaroubiPerfectFactors A D).hom
      (modulePerfectOver A D Set.univ).ι = β.hom := by
    rw [he]
    apply NatTrans.ext
    funext X
    dsimp only [β, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
      isoWhiskerLeft_hom, whiskerLeft_app, finiteCellKaroubiToPerfectCompInclusion,
      ObjectProperty.liftCompιIso]
    simp only [Iso.symm_hom, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
    let a := (finiteCellKaroubiRealization_fac A D Set.univ).hom.app X
    exact (show a = 𝟙 _ ≫ 𝟙 _ ≫ a ≫ 𝟙 _ from by
      simp only [Category.id_comp, Category.comp_id])
  exact NatTrans.CommShift.of_comp_faithful
    (F₁ := toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ)
    (F₂ := triaToPerfect A D) (τ := (triaKaroubiPerfectFactors A D).hom)
    (G := (modulePerfectOver A D Set.univ).ι) (h := by rw [he']; exact hβ)

variable {A' : Type u} [CommRing A'] (E : Type w) [DGCategory A' E] [Small.{u} E]
  (G : TriaCategory A D ⥤ TriaCategory A' E) [G.CommShift ℤ]
  (T : PerfectModuleCategory A D ⥤ PerfectModuleCategory A' E) [T.CommShift ℤ]
  (e : G ⋙ triaToPerfect A' E ≅ triaToPerfect A D ⋙ T) [NatTrans.CommShift e.hom ℤ]

def triaKaroubiPerfectRestrictedSquare :
    toKaroubi (TriaCategory A D) ⋙
        ((functorExtension₂ _ _).obj G ⋙ finiteCellKaroubiToPerfect A' E Set.univ) ≅
      toKaroubi (TriaCategory A D) ⋙ (finiteCellKaroubiToPerfect A D Set.univ ⋙ T) :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (G := toKaroubi (TriaCategory A D) ⋙ (functorExtension₂ _ _).obj G)
      (H := G ⋙ toKaroubi (TriaCategory A' E))
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft G (triaKaroubiPerfectFactors A' E) ≪≫ e ≪≫
    isoWhiskerRight (triaKaroubiPerfectFactors A D).symm T ≪≫ Functor.associator _ _ _

instance triaKaroubiPerfectRestrictedSquareCommShift :
    NatTrans.CommShift (triaKaroubiPerfectRestrictedSquare A D E G T e).hom ℤ := by
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A D) ⋙ (functorExtension₂ _ _).obj G ⟶
        G ⋙ toKaroubi (TriaCategory A' E) from
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G).hom) ℤ :=
    karoubiExtensionFactors_commShift G
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A D) ⋙ finiteCellKaroubiToPerfect A D Set.univ ⟶
        triaToPerfect A D from (triaKaroubiPerfectFactors A D).hom) ℤ :=
    triaKaroubiPerfectFactorsCommShift A D
  let : NatTrans.CommShift
      (show toKaroubi (TriaCategory A' E) ⋙ finiteCellKaroubiToPerfect A' E Set.univ ⟶
        triaToPerfect A' E from (triaKaroubiPerfectFactors A' E).hom) ℤ :=
    triaKaroubiPerfectFactorsCommShift A' E
  dsimp only [triaKaroubiPerfectRestrictedSquare, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

instance triaKaroubiPerfectSquareCommShift :
    NatTrans.CommShift (triaKaroubiPerfectSquare A D E G T e).hom ℤ := by
  let ff := whiskeringLeftObjToKaroubiFullyFaithful
    (C := TriaCategory A D) (D := PerfectModuleCategory A' E)
  let := ff.faithful
  refine natTransCommShift_of_precomp (toKaroubi (TriaCategory A D)) _ (hτ := ?_)
  have he : whiskerLeft (toKaroubi (TriaCategory A D))
      (triaKaroubiPerfectSquare A D E G T e).hom =
      (triaKaroubiPerfectRestrictedSquare A D E G T e).hom := ff.map_preimage _
  rw [he]
  infer_instance
end SerrePositivity.DifferentialGraded
end

end KaroubiSquareShift

/-! ## KaroubiMapShift（旧 SerrePositivity/DifferentialGraded/Verdier/KaroubiMapShift.lean） -/

/-! # Karoubi 延長の合成比較と自然同型の shift 整合性 -/

@[expose] public section KaroubiMapShift

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable {C E T : Type*} [Category* C] [Category* E] [Category* T]
  [HasShift C ℤ] [HasShift E ℤ] [HasShift T ℤ]

/-- 元の Karoubi 因子化を、合成関手を明記した型で用いる。 -/
def karoubiFactor (F : C ⥤ E) :
    toKaroubi C ⋙ (functorExtension₂ C E).obj F ≅ F ⋙ toKaroubi E :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso C E).app F

instance karoubiFactorCommShift (F : C ⥤ E) [F.CommShift ℤ] :
    NatTrans.CommShift (karoubiFactor F).hom ℤ := karoubiExtensionFactors_commShift F

variable (F : C ⥤ E) [F.CommShift ℤ] (G : E ⥤ T) [G.CommShift ℤ]

def karoubiCompositionRestrictedSquare :
    toKaroubi C ⋙ ((functorExtension₂ C E).obj F ⋙ (functorExtension₂ E T).obj G) ≅
      toKaroubi C ⋙ (functorExtension₂ C T).obj (F ⋙ G) :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (karoubiFactor F) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft F (karoubiFactor G) ≪≫
    (Functor.associator _ _ _).symm ≪≫ (karoubiFactor (F ⋙ G)).symm

instance karoubiCompositionRestrictedSquareCommShift :
    NatTrans.CommShift (karoubiCompositionRestrictedSquare F G).hom ℤ := by
  dsimp only [karoubiCompositionRestrictedSquare, Iso.trans_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom]
  infer_instance

omit [HasShift C ℤ] [HasShift E ℤ] [HasShift T ℤ] [F.CommShift ℤ] [G.CommShift ℤ] in
lemma karoubiComposition_whisker :
    whiskerLeft (toKaroubi C) (karoubiFunctorCompositionIso F G).hom =
      (karoubiCompositionRestrictedSquare F G).hom := by
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [comp_obj, karoubiFunctorCompositionIso, Iso.refl_hom, whiskerLeft_id', NatTrans.id_app,
    Karoubi.id_f, functorExtension₂_obj_obj_p, toKaroubi_obj_X, toKaroubi_obj_p, map_id,
    karoubiCompositionRestrictedSquare, karoubiFactor, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Iso.app_hom, isoWhiskerLeft_hom, Iso.app_inv, NatTrans.comp_app,
    associator_inv_app, whiskerRight_app, associator_hom_app, whiskerLeft_app, Category.id_comp,
    Karoubi.comp_f, functorExtension₂_obj_map_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_hom_app_app_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_inv_app_app_f, Category.comp_id]
  exact (Category.comp_id _).symm

instance karoubiFunctorCompositionIsoCommShift :
    NatTrans.CommShift (karoubiFunctorCompositionIso F G).hom ℤ := by
  let := (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi T)).faithful
  refine natTransCommShift_of_precomp (toKaroubi C) _ (hτ := ?_)
  rw [karoubiComposition_whisker]
  infer_instance

section Map
variable {F G} {F' : C ⥤ E} [F'.CommShift ℤ] (α : F ≅ F') [NatTrans.CommShift α.hom ℤ]

def karoubiMapRestrictedSquare :
    toKaroubi C ⋙ (functorExtension₂ C E).obj F ≅
      toKaroubi C ⋙ (functorExtension₂ C E).obj F' :=
  karoubiFactor F ≪≫ isoWhiskerRight α (toKaroubi E) ≪≫ (karoubiFactor F').symm

instance karoubiMapRestrictedSquareCommShift :
    NatTrans.CommShift (karoubiMapRestrictedSquare α).hom ℤ := by
  dsimp only [karoubiMapRestrictedSquare, Iso.trans_hom, isoWhiskerRight_hom]
  infer_instance

omit [HasShift C ℤ] [HasShift E ℤ] [F.CommShift ℤ] [F'.CommShift ℤ]
    [NatTrans.CommShift α.hom ℤ] in
lemma karoubiMap_whisker :
    whiskerLeft (toKaroubi C) ((functorExtension₂ C E).mapIso α).hom =
      (karoubiMapRestrictedSquare α).hom := by
  apply NatTrans.ext
  funext X
  apply Karoubi.hom_ext
  simp only [comp_obj, mapIso_hom, whiskerLeft_app, functorExtension₂_map_app_f, toKaroubi_obj_X,
    toKaroubi_obj_p, map_id, Category.comp_id, karoubiMapRestrictedSquare, karoubiFactor,
    Iso.trans_hom, Iso.app_hom, isoWhiskerRight_hom, Iso.symm_hom, Iso.app_inv,
    NatTrans.comp_app, whiskerRight_app, Karoubi.comp_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_hom_app_app_f, toKaroubi_map_f,
    functorExtension₂CompWhiskeringLeftToKaroubiIso_inv_app_app_f]
  exact (Category.id_comp (α.hom.app X)).symm

instance karoubiMapIsoCommShift :
    NatTrans.CommShift ((functorExtension₂ C E).mapIso α).hom ℤ := by
  let := (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := Karoubi E)).faithful
  refine natTransCommShift_of_precomp (toKaroubi C) _ (hτ := ?_)
  rw [karoubiMap_whisker]
  infer_instance
end Map

variable {E' : Type*} [Category* E'] [HasShift E' ℤ]
  {F' : C ⥤ E'} {G' : E' ⥤ T} [F'.CommShift ℤ] [G'.CommShift ℤ]
  (e : F ⋙ G ≅ F' ⋙ G') [NatTrans.CommShift e.hom ℤ]

instance karoubiFunctorSquareCommShift : NatTrans.CommShift (karoubiFunctorSquare F G e).hom ℤ := by
  dsimp only [karoubiFunctorSquare, Iso.trans_hom]
  infer_instance
end SerrePositivity.DifferentialGraded
end

end KaroubiMapShift

/-! ## ScalarKaroubiShift（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarKaroubiShift.lean） -/

/-! # 非平坦係数変更の tria–Perf・Karoubi–Perf 正方形の shift 整合性 -/

@[expose] public section ScalarKaroubiShift
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

instance quotientScalarTriaPerfectSquareCommShift :
    NatTrans.CommShift (quotientScalarTriaPerfectSquare φ S).hom ℤ := by
  let Q := QuotientObject D S
  let Q' := QuotientObject (DGBaseChange φ D) S
  let I := (modulePerfectOver A' Q' Set.univ).ι
  let H := triaToPerfect A Q ⋙ quotientScalarPerfectFunctor φ D S ⋙ I
  let β : (quotientScalarTriaFunctor φ S ⋙ triaToPerfect A' Q') ⋙ I ≅
      (triaToPerfect A Q ⋙ quotientScalarPerfectFunctor φ D S) ⋙ I :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ ((modulePerfectOver A' Q' Set.univ).liftCompιIso (triaInclusion A' Q') _) ≪≫
      (derivedFiniteCellOver A' Q' Set.univ).liftCompιIso H
        (quotientScalarPerfect_tria φ S) ≪≫ (Functor.associator _ _ _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by dsimp [β]; infer_instance
  have he : whiskerRight (quotientScalarTriaPerfectSquare φ S).hom I = β.hom := by
    apply NatTrans.ext
    funext X
    dsimp only [β, quotientScalarTriaPerfectSquare, whiskerRight_app, Iso.refl_hom,
      NatTrans.id_app, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
      associator_inv_app, isoWhiskerLeft_hom, whiskerLeft_app, ObjectProperty.liftCompιIso]
    rw [CategoryTheory.Functor.map_id]
    exact (show 𝟙 (H.obj X) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ from by
      simp only [Category.id_comp])
  exact NatTrans.CommShift.of_comp_faithful (τ := (quotientScalarTriaPerfectSquare φ S).hom)
    (G := I) (h := by rw [he]; exact hβ)

instance quotientScalarKaroubiPerfectSquareCommShift :
    NatTrans.CommShift (quotientScalarKaroubiPerfectSquare φ S).hom ℤ := by
  dsimp only [quotientScalarKaroubiPerfectSquare]
  infer_instance

def quotientScalarKaroubiPerfectSquareTriangle :=
  Functor.mapTriangleIso (quotientScalarKaroubiPerfectSquare φ S)
end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarKaroubiShift

/-! ## GraphPerfectSquare（旧 SerrePositivity/DifferentialGraded/Verdier/GraphPerfectSquare.lean） -/

/-! # 誘導 Verdier 関手・Karoubi 完備化・perfect enhancement と graph 作用の自然性 -/

@[expose] public section GraphPerfectSquare
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C C' P P' : Type*} [Category* C] [Category* C'] [Category* P] [Category* P']
  (e : C ≌ P) (e' : C' ≌ P') (F : C ⥤ C') (T : P ⥤ P')

/-- 比較同値の順方向の正方形から、逆方向の正方形を得る。 -/
def equivalenceInverseSquare (α : F ⋙ e'.functor ≅ e.functor ⋙ T) :
    e.inverse ⋙ F ≅ T ⋙ e'.inverse :=
  ((whiskeringRight _ _ _).obj e'.functor).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso T ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft T e'.counitIso.symm ≪≫ (Functor.associator _ _ _).symm)
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance graphPerfectSquareExtensionCommShift :
    (quasiEquivalencePerfectExtension A D E F).CommShift ℤ :=
  quasiEquivalencePerfectExtensionCommShift A D E F
local instance graphPerfectSquareExtensionIsTriangulated :
    (quasiEquivalencePerfectExtension A D E F).IsTriangulated :=
  quasiEquivalencePerfectExtensionIsTriangulated A D E F

def graphTriaPerfectSquare :
    graphTriaFunctor A D E F ⋙ triaToPerfect A E ≅
      triaToPerfect A D ⋙ quasiEquivalencePerfectExtension A D E F := Iso.refl _

def graphKaroubiPerfectSquare :
    (functorExtension₂ _ _).obj (graphTriaFunctor A D E F) ⋙
        finiteCellKaroubiToPerfect A E Set.univ ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ quasiEquivalencePerfectExtension A D E F :=
  triaKaroubiPerfectSquare A D E _ _ (graphTriaPerfectSquare A D E F)

variable (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)
  (hD : localKFlat A D S) (hE : localKFlat A E T)

/-- 元の tria 上で誘導してから、指定 Karoubi 完備化を取った関手。 -/
def graphCompletedVerdierFunctor : CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A E T :=
  (functorExtension₂ _ _).obj (graphVerdierFunctor A D E F S T hF)

instance graphCompletedVerdierFunctorCommShift :
    (graphCompletedVerdierFunctor A D E F S T hF).CommShift ℤ := by
  dsimp [graphCompletedVerdierFunctor]
  infer_instance
instance graphCompletedVerdierFunctorIsTriangulated :
    (graphCompletedVerdierFunctor A D E F S T hF).IsTriangulated := by
  dsimp [graphCompletedVerdierFunctor]
  infer_instance

/-- 局所商比較の完備化は、実際に誘導した完備 Verdier 関手と可換する。 -/
def graphCompletedVerdierSquare :
    graphCompletedVerdierFunctor A D E F S T hF ⋙
        (localCompletedQuotientEquivalence A E T hE).functor ≅
      (localCompletedQuotientEquivalence A D S hD).functor ⋙
        (functorExtension₂ _ _).obj
          (graphTriaFunctor A (QuotientObject D S) (QuotientObject E T)
            (quotientDGFunctor A D E F S T hF)) :=
  karoubiFunctorSquare _ _ (graphLocalVerdierSquare A D E F S T hF)

/-- 完備商から主 Perf への、既存の二つの同値の合成。 -/
def graphCompletedPerfectComparison : CompletedTriaQuotient A D S ≌
    PerfectModuleCategory A (QuotientObject D S) :=
  (localCompletedQuotientEquivalence A D S hD).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ)

def graphCompletedPerfectSquare :
    graphCompletedVerdierFunctor A D E F S T hF ⋙
        (graphCompletedPerfectComparison A E T hE).functor ≅
      (graphCompletedPerfectComparison A D S hD).functor ⋙
        quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (graphCompletedVerdierSquare A D E F S T hF hD hE) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (graphKaroubiPerfectSquare A (QuotientObject D S) (QuotientObject E T)
      (quotientDGFunctor A D E F S T hF)) ≪≫ (Functor.associator _ _ _).symm

/-- 実際の商 dg 関手の導来 graph 作用を、既存 enhancement の H⁰ へ運ぶ。 -/
def graphQuotientPerfectHomotopyFunctor :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ⥤
      PerfectDGHomotopyCategoryOver A (QuotientObject E T) Set.univ :=
  (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
      (quotientDGFunctor A D E F S T hF) ⋙
    (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).inverse

instance graphQuotientPerfectHomotopyFunctorCommShift :
    (graphQuotientPerfectHomotopyFunctor A D E F S T hF).CommShift ℤ := by
  dsimp [graphQuotientPerfectHomotopyFunctor]
  infer_instance
instance graphQuotientPerfectHomotopyFunctorIsTriangulated :
    (graphQuotientPerfectHomotopyFunctor A D E F S T hF).IsTriangulated := by
  dsimp [graphQuotientPerfectHomotopyFunctor]
  infer_instance

def graphQuotientPerfectHomotopySquare :
    graphQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (perfectDGModuleHomotopyEquivalence A (QuotientObject E T) Set.univ).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        quasiEquivalencePerfectExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (perfectDGModuleHomotopyEquivalence A (QuotientObject E T)
      Set.univ).counitIso ≪≫ Functor.rightUnitor _)

instance graphQuotientPerfectHomotopySquareCommShift :
    NatTrans.CommShift (graphQuotientPerfectHomotopySquare A D E F S T hF).hom ℤ := by
  dsimp only [graphQuotientPerfectHomotopySquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

def graphQuotientPerfectHomotopySquareTriangle :=
  Functor.mapTriangleIso (graphQuotientPerfectHomotopySquare A D E F S T hF)

/-- 指定された局所 perfect enhancement 比較そのものの、graph 作用に関する自然性。 -/
def graphLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S hD).functor ⋙
        graphCompletedVerdierFunctor A D E F S T hF ≅
      graphQuotientPerfectHomotopyFunctor A D E F S T hF ⋙
        (localPerfectQuotientEquivalence A E T hE).functor :=
  Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S hD).inverse
      (graphCompletedVerdierFunctor A D E F S T hF) ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S hD) (graphCompletedPerfectComparison A E T hE)
      _ _ (graphCompletedPerfectSquare A D E F S T hF hD hE)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (graphQuotientPerfectHomotopySquare A D E F S T hF).symm _ ≪≫
    Functor.associator _ _ _
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end GraphPerfectSquare

/-! ## GraphKernelSquare（旧 SerrePositivity/DifferentialGraded/Verdier/GraphKernelSquare.lean） -/

/-! # U16a の実際の通常 graph kernel 作用と dg 商の比較

通常 bimodule 上の主導来作用を使用する。主導来 kernel 全体の未実装の作用は仮定しない。
-/

@[expose] public section GraphKernelSquare
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Morita
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  (S : Set D) (T : Set E) (hF : ∀ d ∈ S, F.obj d ∈ T)

/-- 元の dg 関手と誘導商関手の graph kernel の、全導来対象・射に自然な正方形。 -/
def graphKernelQuotientSquare :
    kernelDerivedTensorOnBimodule A D (QuotientObject D S)
        (functorGraph A D (QuotientObject D S) (inclusion A D S)) ⋙
      kernelDerivedTensorOnBimodule A (QuotientObject D S) (QuotientObject E T)
        (functorGraph A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF)) ≅
    kernelDerivedTensorOnBimodule A D E (functorGraph A D E F) ⋙
      kernelDerivedTensorOnBimodule A E (QuotientObject E T)
        (functorGraph A E (QuotientObject E T) (inclusion A E T)) :=
  graphDerivedQuotientSquare A D E F S T hF

lemma graphKernelQuotientSquare_naturality
    {X Y : DerivedModuleCategory A D} (f : X ⟶ Y) :
    (dgDerivedExtension A D (QuotientObject D S) (inclusion A D S) ⋙
        dgDerivedExtension A (QuotientObject D S) (QuotientObject E T)
          (quotientDGFunctor A D E F S T hF)).map f ≫
        (graphKernelQuotientSquare A D E F S T hF).hom.app Y =
      (graphKernelQuotientSquare A D E F S T hF).hom.app X ≫
        (dgDerivedExtension A D E F ⋙
          dgDerivedExtension A E (QuotientObject E T) (inclusion A E T)).map f :=
  (graphKernelQuotientSquare A D E F S T hF).hom.naturality f
end SerrePositivity.DifferentialGraded.DGQuotient
end

end GraphKernelSquare

/-! ## PerfectNullComparison（旧 SerrePositivity/DifferentialGraded/Verdier/PerfectNullComparison.lean） -/

/-! # Karoubi-first の厚い零部分圏と指定 Perf 部分圏の同定 -/

@[expose] public section PerfectNullComparison
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D)

instance perfectNullObjectsClosedUnderIso :
    (perfectNullObjects A D S).IsClosedUnderIsomorphisms := by
  dsimp [perfectNullObjects]
  infer_instance

instance perfectNullObjectsStableUnderRetracts :
    (perfectNullObjects A D S).IsStableUnderRetracts where
  of_retract r hY :=
    (modulePerfectOver A D S).prop_of_retract (r.map (modulePerfectOver A D Set.univ).ι) hY

/-- 完備化を先に行う側の零部分圏は、実際の Perf_S の逆像と一致する。 -/
lemma karoubiNullEnvelope_eq_perfectNull :
    karoubiNullEnvelope (triaImage A D S) =
      (perfectNullObjects A D S).inverseImage (finiteCellKaroubiToPerfect A D Set.univ) := by
  let F := finiteCellKaroubiToPerfect A D Set.univ
  let N := (perfectNullObjects A D S).inverseImage F
  have : N.IsTriangulated := by dsimp [N, F]; infer_instance
  have : N.IsStableUnderRetracts :=
    ⟨fun r hY => (perfectNullObjects A D S).prop_of_retract (r.map F) hY⟩
  apply le_antisymm
  · change ((triaImage A D S).map (toKaroubi (TriaCategory A D))).triangEnvelope ≤ N
    apply (((triaImage A D S).map (toKaroubi (TriaCategory A D))).triangEnvelope_le_iff
      (Q := N)).2
    rintro X ⟨Y, hY, ⟨e⟩⟩
    apply N.prop_of_iso e
    exact (perfectNullObjects A D S).prop_of_iso
      ((triaKaroubiPerfectFactors A D).app Y).symm
      ((derivedFiniteCellOver A D S).le_retractClosure _ hY)
  · intro X hX
    obtain ⟨Y, hY, ⟨r⟩⟩ := hX
    have hYu : derivedFiniteCellOver A D Set.univ Y :=
      ObjectProperty.map_monotone
        (fun _ hM => moduleFiniteCellOver_mono A D (Set.subset_univ S) hM)
        (moduleToDerived A D) Y hY
    let Y' : TriaCategory A D := ⟨Y, hYu⟩
    let rP : Retract (F.obj X) ((triaToPerfect A D).obj Y') :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := by apply (modulePerfectOver A D Set.univ).hom_ext; exact r.retract }
    let rK : Retract X ((toKaroubi (TriaCategory A D)).obj Y') :=
      comparisonRetractPreimage F
        (rP.trans (Retract.ofIso ((triaKaroubiPerfectFactors A D).app Y').symm))
    apply (karoubiNullEnvelope (triaImage A D S)).prop_of_retract rK
    exact ((triaImage A D S).map (toKaroubi (TriaCategory A D))).le_triangEnvelope _
      ((triaImage A D S).prop_map_obj (toKaroubi (TriaCategory A D)) hY)

lemma karoubiNullEnvelope_iff_perfect (X : Karoubi (TriaCategory A D)) :
    karoubiNullEnvelope (triaImage A D S) X ↔
      modulePerfectOver A D S ((finiteCellKaroubiToPerfect A D Set.univ).obj X).obj := by
  rw [karoubiNullEnvelope_eq_perfectNull A D S]
  rfl

/-- 零部分圏の同定は対象だけでなく、その充満部分圏の同値を与える。 -/
def perfectNullEquivalence :
    (karoubiNullEnvelope (triaImage A D S)).FullSubcategory ≌
      (perfectNullObjects A D S).FullSubcategory :=
  (finiteCellKaroubiPerfectEquivalence A D Set.univ).congrFullSubcategory
    (karoubiNullEnvelope_eq_perfectNull A D S).symm
end SerrePositivity.DifferentialGraded
end

end PerfectNullComparison

/-! ## PerfectQuotientEquivalence（旧 SerrePositivity/DifferentialGraded/Verdier/PerfectQuotientEquivalence.lean） -/

/-! # 指定 Perf 商と既存 Karoubi-first 商・局所 perfect dg 商比較の同値 -/

@[expose] public section PerfectQuotientEquivalence
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)

lemma karoubiPerfect_denominators :
    (karoubiNullEnvelope (triaImage A D S)).trW =
      (perfectNullObjects A D S).trW.inverseImage (finiteCellKaroubiToPerfect A D Set.univ) := by
  rw [karoubiNullEnvelope_eq_perfectNull A D S]
  ext X Y f
  exact (perfectNullObjects A D S).inverseImage_trW_iff _ f

def karoubiPerfectLocalizer :
    LocalizerMorphism (karoubiNullEnvelope (triaImage A D S)).trW
      (perfectNullObjects A D S).trW :=
  LocalizerMorphism.ofEq (karoubiPerfect_denominators A D S)

instance karoubiPerfectLocalizerIsLocalizedEquivalence :
    (karoubiPerfectLocalizer A D S).IsLocalizedEquivalence := by
  let Φ := karoubiPerfectLocalizer A D S
  have : Φ.functor.IsEquivalence := finiteCellKaroubiToPerfectIsEquivalence A D Set.univ
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ
  change (perfectNullObjects A D S).trW ≤
    (karoubiNullEnvelope (triaImage A D S)).trW.map (finiteCellKaroubiToPerfect A D Set.univ)
  rw [karoubiPerfect_denominators, MorphismProperty.map_inverseImage_eq_of_isEquivalence]

def karoubiFirstPerfectQuotientFunctor :
    KaroubiFirstQuotient (triaImage A D S) ⥤ PerfectVerdierQuotient A D S :=
  (karoubiPerfectLocalizer A D S).localizedFunctor
    (karoubiNullEnvelope (triaImage A D S)).trW.Q (perfectVerdierQuotient A D S)

instance karoubiFirstPerfectQuotientLifting :
    Localization.Lifting (karoubiNullEnvelope (triaImage A D S)).trW.Q
      (karoubiNullEnvelope (triaImage A D S)).trW
      (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
      (karoubiFirstPerfectQuotientFunctor A D S) := by
  change Localization.Lifting _ _
    ((karoubiPerfectLocalizer A D S).functor ⋙ perfectVerdierQuotient A D S)
    ((karoubiPerfectLocalizer A D S).localizedFunctor _ _)
  infer_instance

instance karoubiFirstPerfectQuotientFunctorIsEquivalence :
    (karoubiFirstPerfectQuotientFunctor A D S).IsEquivalence := by
  dsimp [karoubiFirstPerfectQuotientFunctor]
  infer_instance

def karoubiFirstPerfectQuotientEquivalence :
    KaroubiFirstQuotient (triaImage A D S) ≌ PerfectVerdierQuotient A D S :=
  (karoubiFirstPerfectQuotientFunctor A D S).asEquivalence

/-- 既存 Karoubi–Perf 同値を先に局所化した、指定商関手との正方形。 -/
def karoubiFirstPerfectQuotientSquare :
    (karoubiNullEnvelope (triaImage A D S)).trW.Q ⋙
        karoubiFirstPerfectQuotientFunctor A D S ≅
      finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S :=
  Localization.Lifting.iso _ (karoubiNullEnvelope (triaImage A D S)).trW _ _

instance karoubiFirstPerfectQuotientFunctorCommShift :
    (karoubiFirstPerfectQuotientFunctor A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW ℤ
    (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
    (karoubiFirstPerfectQuotientFunctor A D S)

instance karoubiFirstPerfectQuotientSquareCommShift :
    NatTrans.CommShift (karoubiFirstPerfectQuotientSquare A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW ℤ
    (finiteCellKaroubiToPerfect A D Set.univ ⋙ perfectVerdierQuotient A D S)
    (karoubiFirstPerfectQuotientFunctor A D S)

instance karoubiFirstPerfectQuotientFunctorIsTriangulated :
    (karoubiFirstPerfectQuotientFunctor A D S).IsTriangulated := by
  have := Localization.essSurj_mapArrow (karoubiNullEnvelope (triaImage A D S)).trW.Q
    (karoubiNullEnvelope (triaImage A D S)).trW
  exact Functor.isTriangulated_of_precomp_iso (karoubiFirstPerfectQuotientSquare A D S)

instance karoubiFirstPerfectQuotientEquivalenceFunctorCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).functor.CommShift ℤ :=
  karoubiFirstPerfectQuotientFunctorCommShift A D S
instance karoubiFirstPerfectQuotientEquivalenceInverseCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).inverse.CommShift ℤ :=
  (karoubiFirstPerfectQuotientEquivalence A D S).commShiftInverse ℤ
instance karoubiFirstPerfectQuotientEquivalenceCommShift :
    (karoubiFirstPerfectQuotientEquivalence A D S).CommShift ℤ :=
  (karoubiFirstPerfectQuotientEquivalence A D S).commShift_of_functor ℤ
instance karoubiFirstPerfectQuotientEquivalenceIsTriangulated :
    (karoubiFirstPerfectQuotientEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (karoubiFirstPerfectQuotientFunctorIsTriangulated A D S)

instance karoubiPerfectCompletedFunctorCommShift :
    (karoubiEquivalenceTransport
      (karoubiFirstPerfectQuotientEquivalence A D S)).functor.CommShift ℤ := by
  change ((functorExtension₂ _ _).obj
    (karoubiFirstPerfectQuotientEquivalence A D S).functor).CommShift ℤ
  infer_instance
instance karoubiPerfectCompletedInverseCommShift :
    (karoubiEquivalenceTransport
      (karoubiFirstPerfectQuotientEquivalence A D S)).inverse.CommShift ℤ :=
  (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).commShiftInverse ℤ
instance karoubiPerfectCompletedCommShift :
    (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).CommShift ℤ :=
  (karoubiEquivalenceTransport
    (karoubiFirstPerfectQuotientEquivalence A D S)).commShift_of_functor ℤ
instance karoubiPerfectCompletedIsTriangulated :
    (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change ((functorExtension₂ _ _).obj
      (karoubiFirstPerfectQuotientEquivalence A D S).functor).IsTriangulated
    infer_instance)

/-- 既存の完備化順序交換同値に接続した、指定 Perf 商の完備化。 -/
def perfectCompletedToTriaQuotientEquivalence :
    Karoubi (PerfectVerdierQuotient A D S) ≌ CompletedTriaQuotient A D S :=
  (karoubiEquivalenceTransport (karoubiFirstPerfectQuotientEquivalence A D S)).symm.trans
    (triaKaroubiOrderEquivalence A D S)

instance perfectCompletedToTriaQuotientFunctorCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).functor.CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientInverseCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).inverse.CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientCommShift :
    (perfectCompletedToTriaQuotientEquivalence A D S).CommShift ℤ := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance
instance perfectCompletedToTriaQuotientIsTriangulated :
    (perfectCompletedToTriaQuotientEquivalence A D S).IsTriangulated := by
  dsimp [perfectCompletedToTriaQuotientEquivalence]
  infer_instance

namespace DGQuotient
/-- 同じ指定商に値を持つ局所 perfect dg 商比較を、指定 Perf 商の完備化へ接続する。 -/
def localPerfectToPerfectVerdierEquivalence (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      Karoubi (PerfectVerdierQuotient A D S) :=
  (localPerfectQuotientEquivalence A D S h).trans
    (perfectCompletedToTriaQuotientEquivalence A D S).symm

instance localPerfectToPerfectVerdierFunctorCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierInverseCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).inverse.CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierCommShift (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).CommShift ℤ := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
instance localPerfectToPerfectVerdierIsTriangulated (h : localKFlat A D S) :
    (localPerfectToPerfectVerdierEquivalence A D S h).IsTriangulated := by
  dsimp [localPerfectToPerfectVerdierEquivalence]
  infer_instance
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end PerfectQuotientEquivalence

/-! ## ScalarCompletionSquare（旧 SerrePositivity/DifferentialGraded/Verdier/ScalarCompletionSquare.lean） -/

/-! # 係数変更の tria 完備化と既存の perfect 比較による構成の一致 -/

@[expose] public section ScalarCompletionSquare
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory CategoryTheory.Functor Idempotents ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D] (S : Set D)
  (h : localKFlat A D S) (h' : localKFlat A' (DGBaseChange φ D) S)

/-- 未完備の指定商上の係数変更を、元の Karoubi 関手延長で完備化する。 -/
def scalarCompletedTriaFunctor :
    CompletedTriaQuotient A D S ⥤ CompletedTriaQuotient A' (DGBaseChange φ D) S :=
  (functorExtension₂ _ _).obj (localScalarTriaExtension φ S h h')

instance scalarCompletedTriaFunctorCommShift :
    (scalarCompletedTriaFunctor φ D S h h').CommShift ℤ := by
  dsimp [scalarCompletedTriaFunctor]
  infer_instance
instance scalarCompletedTriaFunctorIsTriangulated :
    (scalarCompletedTriaFunctor φ D S h h').IsTriangulated := by
  dsimp [scalarCompletedTriaFunctor]
  infer_instance

def scalarCompletedTriaSquare :
    scalarCompletedTriaFunctor φ D S h h' ⋙
        (localCompletedQuotientEquivalence A' (DGBaseChange φ D) S h').functor ≅
      (localCompletedQuotientEquivalence A D S h).functor ⋙
        (functorExtension₂ _ _).obj (quotientScalarTriaFunctor φ S) :=
  karoubiFunctorSquare _ _ (localScalarTriaSquare φ S h h')

def scalarCompletedPerfectSquare :
    scalarCompletedTriaFunctor φ D S h h' ⋙
        (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h').functor ≅
      (graphCompletedPerfectComparison A D S h).functor ⋙ quotientScalarPerfectFunctor φ D S :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (scalarCompletedTriaSquare φ D S h h') _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (quotientScalarKaroubiPerfectSquare φ S) ≪≫
    (Functor.associator _ _ _).symm

/-- 完備化した tria 係数変更と、指定局所 perfect 同値の実際の正方形。 -/
def scalarCompletedLocalPerfectSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ scalarCompletedTriaFunctor φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (DGBaseChange φ D) S h').functor :=
  Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S h).inverse (scalarCompletedTriaFunctor φ D S h h') ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S h)
      (graphCompletedPerfectComparison A' (DGBaseChange φ D) S h') _ _
      (scalarCompletedPerfectSquare φ D S h h')) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientScalarPerfectHomotopySquare φ D S).symm _ ≪≫
    Functor.associator _ _ _

/-- tria を先に完備化する経路と、既存 perfect 比較で運ぶ経路は同じ係数変更を与える。 -/
def scalarCompletionComparisonIso :
    scalarCompletedTriaFunctor φ D S h h' ≅ completedScalarExtension φ D S h h' :=
  ((localPerfectQuotientEquivalence A D S h).congrLeft
    (E := CompletedTriaQuotient A' (DGBaseChange φ D) S)).inverse.preimageIso
      (scalarCompletedLocalPerfectSquare φ D S h h' ≪≫
        (localPerfectScalarExtensionSquare φ D S h h').symm)

/-- 未完備の指定商からの標準包含に対する、実際の Karoubi 完備化の係数変更正方形。 -/
def scalarCompletionToKaroubiSquare :
    toKaroubi (TriaQuotient A D S) ⋙ completedScalarExtension φ D S h h' ≅
      localScalarTriaExtension φ S h h' ⋙ toKaroubi (TriaQuotient A' (DGBaseChange φ D) S) :=
  isoWhiskerLeft _ (scalarCompletionComparisonIso φ D S h h').symm ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (localScalarTriaExtension φ S h h')
end SerrePositivity.DifferentialGraded.DGQuotient
end

end ScalarCompletionSquare

/-! ## CompletionSquareShift（旧 SerrePositivity/DifferentialGraded/Verdier/CompletionSquareShift.lean） -/

/-! # 係数変更の完備化経路比較の shift 整合性 -/

@[expose] public section CompletionSquareShift
universe u v

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor Idempotents

section General
variable {C C' P P' : Type*} [Category* C] [Category* C'] [Category* P] [Category* P']
  [HasShift C ℤ] [HasShift C' ℤ] [HasShift P ℤ] [HasShift P' ℤ]
  (e : C ≌ P) (e' : C' ≌ P') [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
  [e.CommShift ℤ] [e'.functor.CommShift ℤ] [e'.inverse.CommShift ℤ] [e'.CommShift ℤ]
  (F : C ⥤ C') (T : P ⥤ P') [F.CommShift ℤ] [T.CommShift ℤ]
  (α : F ⋙ e'.functor ≅ e.functor ⋙ T) [NatTrans.CommShift α.hom ℤ]

instance equivalenceInverseSquareCommShift :
    NatTrans.CommShift (equivalenceInverseSquare e e' F T α).hom ℤ := by
  let β : (e.inverse ⋙ F) ⋙ e'.functor ≅ (T ⋙ e'.inverse) ⋙ e'.functor :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft e.inverse α ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso T ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft T e'.counitIso.symm ≪≫ (Functor.associator _ _ _).symm
  have hβ : NatTrans.CommShift β.hom ℤ := by
    dsimp only [β, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom]
    infer_instance
  refine NatTrans.CommShift.of_comp_faithful (G := e'.functor) (h := ?_)
  have he : whiskerRight (equivalenceInverseSquare e e' F T α).hom e'.functor = β.hom :=
    ((whiskeringRight _ _ _).obj e'.functor).map_preimage _
  rw [he]
  exact hβ
end General

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (S : Set D) (h : localKFlat A D S)

instance graphCompletedPerfectComparisonFunctorCommShift :
    (graphCompletedPerfectComparison A D S h).functor.CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance
instance graphCompletedPerfectComparisonInverseCommShift :
    (graphCompletedPerfectComparison A D S h).inverse.CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance
instance graphCompletedPerfectComparisonCommShift :
    (graphCompletedPerfectComparison A D S h).CommShift ℤ := by
  dsimp [graphCompletedPerfectComparison]
  infer_instance

def localPerfectComparisonReassociate :
    (localPerfectQuotientEquivalence A D S h).functor ≅
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
        (graphCompletedPerfectComparison A D S h).inverse :=
  Functor.associator _ _ _

instance localPerfectComparisonReassociateCommShift :
    NatTrans.CommShift (localPerfectComparisonReassociate A D S h).hom ℤ := by
  dsimp only [localPerfectComparisonReassociate]
  infer_instance

variable {A D} {A' : Type u} [CommRing A'] (φ : A →+* A')
  (h' : localKFlat A' (ScalarExtension.DGBaseChange φ D) S)

instance scalarCompletedTriaSquareCommShift :
    NatTrans.CommShift (scalarCompletedTriaSquare φ D S h h').hom ℤ := by
  dsimp only [scalarCompletedTriaSquare]
  infer_instance

instance scalarCompletedPerfectSquareCommShift :
    NatTrans.CommShift (scalarCompletedPerfectSquare φ D S h h').hom ℤ := by
  dsimp only [scalarCompletedPerfectSquare, Iso.trans_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom]
  infer_instance

def scalarCompletedLocalPerfectCoherentSquare :
    (localPerfectQuotientEquivalence A D S h).functor ⋙ scalarCompletedTriaFunctor φ D S h h' ≅
      quotientScalarPerfectHomotopyFunctor φ D S ⋙
        (localPerfectQuotientEquivalence A' (ScalarExtension.DGBaseChange φ D) S h').functor :=
  isoWhiskerRight (localPerfectComparisonReassociate A D S h) _ ≪≫
    Functor.associator
      (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
      (graphCompletedPerfectComparison A D S h).inverse (scalarCompletedTriaFunctor φ D S h h') ≪≫
    isoWhiskerLeft _ (equivalenceInverseSquare
      (graphCompletedPerfectComparison A D S h)
      (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h') _ _
      (scalarCompletedPerfectSquare φ D S h h')) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (quotientScalarPerfectHomotopySquare φ D S).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _
      (localPerfectComparisonReassociate A' (ScalarExtension.DGBaseChange φ D) S h').symm

instance scalarCompletedLocalPerfectCoherentSquareCommShift :
    NatTrans.CommShift (scalarCompletedLocalPerfectCoherentSquare S h φ h').hom ℤ := by
  dsimp only [scalarCompletedLocalPerfectCoherentSquare, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom]
  infer_instance

lemma scalarCompletedLocalPerfectCoherentSquare_eq :
    scalarCompletedLocalPerfectCoherentSquare S h φ h' =
      scalarCompletedLocalPerfectSquare φ D S h h' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  dsimp only [scalarCompletedLocalPerfectCoherentSquare, scalarCompletedLocalPerfectSquare,
    localPerfectComparisonReassociate, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app]
  let H := (perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor
  let a := (equivalenceInverseSquare
    (graphCompletedPerfectComparison A D S h)
    (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h') _ _
    (scalarCompletedPerfectSquare φ D S h h')).hom.app (H.obj X)
  let b := (graphCompletedPerfectComparison A' (ScalarExtension.DGBaseChange φ D) S h').inverse.map
    ((quotientScalarPerfectHomotopySquare φ D S).inv.app X)
  let Y := (graphCompletedPerfectComparison A D S h).inverse.obj (H.obj X)
  exact (show (scalarCompletedTriaFunctor φ D S h h').map (𝟙 Y) ≫
      𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ a ≫ 𝟙 _ ≫ b ≫ 𝟙 _ from by
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Category.comp_id])

instance scalarCompletedLocalPerfectSquareCommShift :
    NatTrans.CommShift (scalarCompletedLocalPerfectSquare φ D S h h').hom ℤ := by
  rw [← scalarCompletedLocalPerfectCoherentSquare_eq S h φ h']
  infer_instance

instance scalarCompletionComparisonIsoCommShift :
    NatTrans.CommShift (scalarCompletionComparisonIso φ D S h h').hom ℤ := by
  let L := (localPerfectQuotientEquivalence A D S h).functor
  let ff := (localPerfectQuotientEquivalence A D S h).congrLeft
    (E := CompletedTriaQuotient A' (ScalarExtension.DGBaseChange φ D) S)
  let : ff.inverse.Faithful := inferInstance
  refine natTransCommShift_of_precomp L _ (hτ := ?_)
  have he : whiskerLeft L (scalarCompletionComparisonIso φ D S h h').hom =
      (scalarCompletedLocalPerfectSquare φ D S h h' ≪≫
        (localPerfectScalarExtensionSquare φ D S h h').symm).hom := ff.inverse.map_preimage _
  rw [he]
  dsimp only [Iso.trans_hom]
  infer_instance

def scalarCompletionComparisonTriangle :=
  Functor.mapTriangleIso (scalarCompletionComparisonIso φ D S h h')

instance scalarCompletionToKaroubiSquareCommShift :
    NatTrans.CommShift (scalarCompletionToKaroubiSquare φ D S h h').hom ℤ := by
  let : NatTrans.CommShift
      (show toKaroubi (TriaQuotient A D S) ⋙ scalarCompletedTriaFunctor φ D S h h' ⟶
        localScalarTriaExtension φ S h h' ⋙
          toKaroubi (TriaQuotient A' (ScalarExtension.DGBaseChange φ D) S) from
        ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
          (localScalarTriaExtension φ S h h')).hom) ℤ :=
    karoubiFactorCommShift (localScalarTriaExtension φ S h h')
  dsimp only [scalarCompletionToKaroubiSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

def scalarCompletionToKaroubiSquareTriangle :=
  Functor.mapTriangleIso (scalarCompletionToKaroubiSquare φ D S h h')
end DGQuotient
end SerrePositivity.DifferentialGraded
end

end CompletionSquareShift
