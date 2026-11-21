module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Represented tensor and cotensor for an existing enriched ordinary category

The mapping objects and their functoriality are Mathlib's `eHomFunctor`.
Two existing parametrized adjunctions express tensor/mapping and tensor/cotensor
representability. This supplies all three ordinary Hom equivalences, their
compatibility and naturality; the stronger enriched Hom-object representability
is kept separately in `EnrichedRepresentability`.
-/

@[expose] public section TensorCotensor
universe u v u' v'

open CategoryTheory Opposite

namespace SerrePositivity.Enriched

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  (C : Type u') [Category.{v'} C] [EnrichedOrdinaryCategory V C]

/-- Representability data on the existing enriched category, with no new
Hom object, ordinary category or adjunction type. -/
structure TensorCotensor where
  /-- 係数を固定したテンソル関手。 -/
  tensor : V ⥤ C ⥤ C
  /-- 係数に反変な余テンソル関手。 -/
  cotensor : Vᵒᵖ ⥤ C ⥤ C
  /-- 係数ごとのテンソルと余テンソルの随伴。 -/
  tensorCotensor : tensor ⊣₂ cotensor
  /-- 原対象ごとのテンソルと豊穣 Hom の随伴。 -/
  tensorHom : tensor.flip ⊣₂ eHomFunctor V C

namespace TensorCotensor

variable {V C} (S : TensorCotensor V C)

/-- テンソルから出る射を、係数から豊穣 Hom への射に転置する。 -/
def tensorHomEquiv (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶ Y) ≃ (K ⟶ (X ⟶[V] Y)) :=
  (S.tensorHom.adj X).homEquiv K Y

/-- テンソルから出る射を、余テンソルへの射に転置する。 -/
def tensorCotensorHomEquiv (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶ Y) ≃ (X ⟶ (S.cotensor.obj (op K)).obj Y) :=
  (S.tensorCotensor.adj K).homEquiv X Y

/-- 余テンソルへの射を、係数から豊穣 Hom への射に転置する。 -/
def cotensorHomEquiv (K : V) (X Y : C) :
    (X ⟶ (S.cotensor.obj (op K)).obj Y) ≃ (K ⟶ (X ⟶[V] Y)) :=
  (S.tensorCotensorHomEquiv K X Y).symm.trans (S.tensorHomEquiv K X Y)

lemma homEquiv_compatibility (K : V) (X Y : C) (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.cotensorHomEquiv K X Y (S.tensorCotensorHomEquiv K X Y f) =
      S.tensorHomEquiv K X Y f := by
  simp [cotensorHomEquiv]

lemma tensorHom_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : (S.tensor.obj L).obj X ⟶ Y) :
    S.tensorHomEquiv K X Y ((S.tensor.map a).app X ≫ f) =
      a ≫ S.tensorHomEquiv L X Y f :=
  S.tensorHom.homEquiv_naturality_two a f

lemma tensorHom_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (S.tensor.obj K).obj X' ⟶ Y) :
    S.tensorHomEquiv K X Y ((S.tensor.obj K).map a ≫ f) =
      S.tensorHomEquiv K X' Y f ≫ eHomWhiskerRight V a Y :=
  S.tensorHom.homEquiv_naturality_one a f

lemma tensorHom_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.tensorHomEquiv K X Y' (f ≫ b) =
      S.tensorHomEquiv K X Y f ≫ eHomWhiskerLeft V X b :=
  S.tensorHom.homEquiv_naturality_three b f

lemma tensorCotensor_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : (S.tensor.obj L).obj X ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y ((S.tensor.map a).app X ≫ f) =
      S.tensorCotensorHomEquiv L X Y f ≫ (S.cotensor.map a.op).app Y :=
  S.tensorCotensor.homEquiv_naturality_one a f

lemma tensorCotensor_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : (S.tensor.obj K).obj X' ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y ((S.tensor.obj K).map a ≫ f) =
      a ≫ S.tensorCotensorHomEquiv K X' Y f :=
  S.tensorCotensor.homEquiv_naturality_two a f

lemma tensorCotensor_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    S.tensorCotensorHomEquiv K X Y' (f ≫ b) =
      S.tensorCotensorHomEquiv K X Y f ≫ (S.cotensor.obj (op K)).map b :=
  S.tensorCotensor.homEquiv_naturality_three b f

lemma cotensorHom_naturality_parameter {K L : V} (a : K ⟶ L) (X Y : C)
    (f : X ⟶ (S.cotensor.obj (op L)).obj Y) :
    S.cotensorHomEquiv K X Y (f ≫ (S.cotensor.map a.op).app Y) =
      a ≫ S.cotensorHomEquiv L X Y f := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_one a f
  change ((S.tensorCotensor.adj K).homEquiv X Y).symm
      (f ≫ (S.cotensor.map a.op).app Y) =
    (S.tensor.map a).app X ≫ ((S.tensorCotensor.adj L).homEquiv X Y).symm f at h
  rw [h, tensorHom_naturality_parameter]

lemma cotensorHom_naturality_source (K : V) {X X' : C} (a : X ⟶ X') (Y : C)
    (f : X' ⟶ (S.cotensor.obj (op K)).obj Y) :
    S.cotensorHomEquiv K X Y (a ≫ f) =
      S.cotensorHomEquiv K X' Y f ≫ eHomWhiskerRight V a Y := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_two a f
  change ((S.tensorCotensor.adj K).homEquiv X Y).symm (a ≫ f) =
    (S.tensor.obj K).map a ≫ ((S.tensorCotensor.adj K).homEquiv X' Y).symm f at h
  rw [h, tensorHom_naturality_source]

lemma cotensorHom_naturality_target (K : V) (X : C) {Y Y' : C} (b : Y ⟶ Y')
    (f : X ⟶ (S.cotensor.obj (op K)).obj Y) :
    S.cotensorHomEquiv K X Y' (f ≫ (S.cotensor.obj (op K)).map b) =
      S.cotensorHomEquiv K X Y f ≫ eHomWhiskerLeft V X b := by
  simp only [cotensorHomEquiv, tensorCotensorHomEquiv, Equiv.trans_apply]
  have h := S.tensorCotensor.homEquiv_symm_naturality_three b f
  change ((S.tensorCotensor.adj K).homEquiv X Y').symm
      (f ≫ (S.cotensor.obj (op K)).map b) =
    ((S.tensorCotensor.adj K).homEquiv X Y).symm f ≫ b at h
  rw [h, tensorHom_naturality_target]

/-- テンソル・余テンソル随伴の余単位。 -/
def evaluation (K : V) (Y : C) :
    (S.tensor.obj K).obj ((S.cotensor.obj (op K)).obj Y) ⟶ Y :=
  (S.tensorCotensor.adj K).counit.app Y

/-- テンソル・余テンソル随伴の単位。 -/
def coevaluation (K : V) (X : C) :
    X ⟶ (S.cotensor.obj (op K)).obj ((S.tensor.obj K).obj X) :=
  (S.tensorCotensor.adj K).unit.app X

lemma tensor_triangle (K : V) (X : C) :
    (S.tensor.obj K).map (S.coevaluation K X) ≫ S.evaluation K ((S.tensor.obj K).obj X) =
      𝟙 _ := (S.tensorCotensor.adj K).left_triangle_components X

lemma cotensor_triangle (K : V) (Y : C) :
    S.coevaluation K ((S.cotensor.obj (op K)).obj Y) ≫
      (S.cotensor.obj (op K)).map (S.evaluation K Y) = 𝟙 _ :=
  (S.tensorCotensor.adj K).right_triangle_components Y

end TensorCotensor

end SerrePositivity.Enriched

end TensorCotensor

/-! # The represented enriched tensor unit is naturally the identity -/

@[expose] public section TensorUnit
universe u v u' v'

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.Enriched
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {C : Type u'} [Category.{v'} C] [EnrichedOrdinaryCategory V C]

lemma eHomEquiv_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V f ≫ eHomWhiskerLeft V X g := by
  rw [eHomEquiv_comp, unitors_inv_equal, rightUnitor_inv_comp_tensorHom_assoc]
  rfl

lemma eHomEquiv_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V (f ≫ g) = eHomEquiv V g ≫ eHomWhiskerRight V f Z := by
  rw [eHomEquiv_comp, leftUnitor_inv_comp_tensorHom_assoc]
  rfl

namespace TensorCotensor
variable (S : TensorCotensor V C)

/-- 恒等射の点を、単位によるテンソルからの射に転置する。 -/
def unitMap (X : C) : (S.tensor.obj (𝟙_ V)).obj X ⟶ X :=
  (S.tensorHomEquiv (𝟙_ V) X X).symm (eHomEquiv V (𝟙 X))

lemma unitMap_comp {X Y : C} (f : X ⟶ Y) :
    unitMap S X ≫ f = (S.tensorHomEquiv (𝟙_ V) X Y).symm (eHomEquiv V f) := by
  apply (S.tensorHomEquiv (𝟙_ V) X Y).injective
  rw [S.tensorHom_naturality_target, unitMap, Equiv.apply_symm_apply,
    ← eHomEquiv_postcomp, Category.id_comp, Equiv.apply_symm_apply]

instance unitMap_isIso (X : C) : IsIso (unitMap S X) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let E : (X ⟶ Y) ≃ ((S.tensor.obj (𝟙_ V)).obj X ⟶ Y) :=
    (eHomEquiv V).trans (S.tensorHomEquiv (𝟙_ V) X Y).symm
  have h : (fun f : X ⟶ Y ↦ unitMap S X ≫ f) = E := by
    funext f
    exact unitMap_comp S f
  exact h.symm ▸ E.bijective

lemma unitMap_naturality {X Y : C} (f : X ⟶ Y) :
    (S.tensor.obj (𝟙_ V)).map f ≫ unitMap S Y = unitMap S X ≫ f := by
  apply (S.tensorHomEquiv (𝟙_ V) X Y).injective
  rw [S.tensorHom_naturality_source, unitMap, Equiv.apply_symm_apply,
    ← eHomEquiv_precomp, Category.comp_id, unitMap_comp, Equiv.apply_symm_apply]

/-- 単位係数でテンソルする関手と恒等関手の自然同型。 -/
def unitIso : S.tensor.obj (𝟙_ V) ≅ 𝟭 C :=
  NatIso.ofComponents (fun X ↦ by
    let e := asIso (unitMap S X)
    exact e) (fun {_ _} f ↦ unitMap_naturality S f)

end TensorCotensor
end SerrePositivity.Enriched
end

end TensorUnit

/-!
# Enriched Hom-object representability of tensor and cotensor

Ordinary Hom adjunctions alone do not assert an isomorphism of V-valued Hom
objects. This additional contract records those isomorphisms as natural
isomorphisms in both category variables, their variance in V, and compatibility
with the already chosen ordinary adjunctions. No new enrichment is constructed.
-/

@[expose] public section EnrichedRepresentability
universe u v u' v'

open CategoryTheory Opposite

namespace SerrePositivity.Enriched

variable {V : Type u} [Category.{v} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type u'} [Category.{v'} C] [EnrichedOrdinaryCategory V C]
  (S : TensorCotensor V C)

/-- 豊穣 Hom を係数 K による内部 Hom に入れた二変数関手。 -/
def powerHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  eHomFunctor V C ⋙ (Functor.whiskeringRight C V V).obj (ihom K)

/-- 原対象を K でテンソルしたときの豊穣 Hom 関手。 -/
def tensorEnrichedHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  (S.tensor.obj K).op ⋙ eHomFunctor V C

/-- 終対象を K で余テンソルしたときの豊穣 Hom 関手。 -/
def cotensorEnrichedHom (K : V) : Cᵒᵖ ⥤ C ⥤ V :=
  eHomFunctor V C ⋙ (Functor.whiskeringLeft C C V).obj (S.cotensor.obj (op K))

/-- Full V-valued representability, with all variance and the compatibility of
generalized points with the three ordinary Hom equivalences fixed explicitly. -/
structure EnrichedRepresentability where
  /-- 原対象をテンソルしたときの豊穣 Hom の表示。 -/
  tensorIso (K : V) : tensorEnrichedHom S K ≅ powerHom (C := C) K
  /-- 終対象を余テンソルしたときの豊穣 Hom の表示。 -/
  cotensorIso (K : V) : cotensorEnrichedHom S K ≅ powerHom (C := C) K
  tensor_parameter {K L : V} (a : K ⟶ L) (X Y : C) :
    eHomWhiskerRight V ((S.tensor.map a).app X) Y ≫
        ((tensorIso K).hom.app (op X)).app Y =
      ((tensorIso L).hom.app (op X)).app Y ≫ (MonoidalClosed.pre a).app (X ⟶[V] Y)
  cotensor_parameter {K L : V} (a : K ⟶ L) (X Y : C) :
    eHomWhiskerLeft V X ((S.cotensor.map a.op).app Y) ≫
        ((cotensorIso K).hom.app (op X)).app Y =
      ((cotensorIso L).hom.app (op X)).app Y ≫ (MonoidalClosed.pre a).app (X ⟶[V] Y)
  tensor_points (K : V) (X Y : C) (f : (S.tensor.obj K).obj X ⟶ Y) :
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((tensorIso K).hom.app (op X)).app Y) =
        S.tensorHomEquiv K X Y f
  cotensor_points (K : V) (X Y : C) (f : X ⟶ (S.cotensor.obj (op K)).obj Y) :
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((cotensorIso K).hom.app (op X)).app Y) =
        S.cotensorHomEquiv K X Y f

namespace EnrichedRepresentability

variable {S} (E : EnrichedRepresentability S)

/-- テンソル側の豊穣 Hom の比較を対象対で評価する。 -/
def tensorHomIso (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶[V] Y) ≅ (ihom K).obj (X ⟶[V] Y) :=
  (E.tensorIso K).app (op X) |>.app Y

/-- 余テンソル側の豊穣 Hom の比較を対象対で評価する。 -/
def cotensorHomIso (K : V) (X Y : C) :
    (X ⟶[V] (S.cotensor.obj (op K)).obj Y) ≅ (ihom K).obj (X ⟶[V] Y) :=
  (E.cotensorIso K).app (op X) |>.app Y

/-- The two representing Hom objects compare by their actual natural isomorphisms. -/
def homObjectComparison (K : V) (X Y : C) :
    ((S.tensor.obj K).obj X ⟶[V] Y) ≅ (X ⟶[V] (S.cotensor.obj (op K)).obj Y) :=
  E.tensorHomIso K X Y ≪≫ (E.cotensorHomIso K X Y).symm

/-- On ordinary points this enriched comparison is exactly the chosen
tensor/cotensor adjunction, rather than an unrelated isomorphism. -/
lemma homObjectComparison_points (K : V) (X Y : C)
    (f : (S.tensor.obj K).obj X ⟶ Y) :
    eHomEquiv V f ≫ (E.homObjectComparison K X Y).hom =
      eHomEquiv V (S.tensorCotensorHomEquiv K X Y f) := by
  apply (cancel_mono (E.cotensorHomIso K X Y).hom).1
  change (eHomEquiv V f ≫ (E.tensorHomIso K X Y).hom ≫
      (E.cotensorHomIso K X Y).inv) ≫ (E.cotensorHomIso K X Y).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm.injective
  change (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V f ≫ ((E.tensorIso K).hom.app (op X)).app Y) =
    (MonoidalClosed.curryHomEquiv' (X := K) (Y := X ⟶[V] Y)).symm
      (eHomEquiv V (S.tensorCotensorHomEquiv K X Y f) ≫
        ((E.cotensorIso K).hom.app (op X)).app Y)
  rw [E.tensor_points, E.cotensor_points, S.homEquiv_compatibility]

end EnrichedRepresentability

end SerrePositivity.Enriched

end EnrichedRepresentability

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.3.1.5"] _root_.SerrePositivity.Enriched.TensorCotensor
