module

public import SerrePositivity.EInfinity.Hammock.LocalizationValueNaturality
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FixedObjectWordDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FixedObjectHom

/-!
# 固定対象の相対圏の図式の局所化 Hom への値

概要：元の自由対象と局所化後の対象表示を保つデータから、各 zigzag の値を固定 Hom に戻す。
方針：元の Q による値と対象の等式の移送を合成し、全相対作用素の自然性を証明する。
規約：対象表示の等式を明示し、未知の高次比較を入力にしない。
使われ方：自由相対解像の hammock から既存の局所化 Hom の図式への右比較。
-/

@[expose] public section
universe u uI vI uO
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory CategoryTheory.Limits SimplicialLocalization

variable {I : Type uI} [Category.{vI} I]

structure LocalizationObjects (D : I ⥤ RelativeCategory.{u}) (O : Type uO) where
  original : (i : I) → O → (D.obj i).category
  original_naturality : ∀ {i j : I} (θ : i ⟶ j) (X : O),
    (D.map θ).functor.obj (original i X) = original j X
  localized : (i : I) → O → (D.obj i).weakEquivalences.Localization
  localized_naturality : ∀ {i j : I} (θ : i ⟶ j) (X : O),
    (strictLocalizationMap (D.map θ)).obj (localized i X) = localized j X
  image_eq : ∀ i X, (D.obj i).weakEquivalences.Q.obj (original i X) = localized i X

namespace LocalizationObjects
variable {D : I ⥤ RelativeCategory.{u}} {O : Type uO} (T : LocalizationObjects D O)

def homDiagram (X Y : O) : I ⥤ Type u :=
  FixedObjectHom.functor (D ⋙ strictLocalizationFunctor) T.localized
    (fun θ X => T.localized_naturality θ X) X Y

def homSimplicialDiagram (X Y : O) : I ⥤ SSet.{u} :=
  T.homDiagram X Y ⋙ Functor.const SimplexCategoryᵒᵖ

def hammockDiagram (X Y : O) : I ⥤ SSet.{u} :=
  (graphWordDiagram D T.original (fun θ X => T.original_naturality θ X) X Y).flip ⋙ colim

def value {w : Word} (i : I) {X Y : O}
    (S : Zigzag (D.obj i).weakEquivalences w (T.original i X) (T.original i Y)) :
    T.localized i X ⟶ T.localized i Y :=
  eqToHom (T.image_eq i X).symm ≫
    Zigzag.Value.value (D.obj i).weakEquivalences.Q (D.obj i).weakEquivalences.Q_inverts S ≫
      eqToHom (T.image_eq i Y)

lemma value_naturality {w : Word} {i j : I} (θ : i ⟶ j) {X Y : O}
    (S : Zigzag (D.obj i).weakEquivalences w (T.original i X) (T.original i Y)) :
    T.value j ((Zigzag.Relative.fixedFunctor (D.map θ)
      (T.original_naturality θ X) (T.original_naturality θ Y)).obj S) =
        FixedObjectHom.map (D ⋙ strictLocalizationFunctor) T.localized
          (fun θ X => T.localized_naturality θ X) θ (T.value i S) := by
  apply eq_of_heq
  dsimp only [value, FixedObjectHom.map]
  simp only [CategoryTheory.Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff,
    comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact Zigzag.Value.value_fixed_comparison (D.map θ)
    (D.obj i).weakEquivalences.Q (D.obj i).weakEquivalences.Q_inverts
    (D.obj j).weakEquivalences.Q (D.obj j).weakEquivalences.Q_inverts
    (strictLocalizationMap (D.map θ)) (strictLocalizationMap_fac (D.map θ))
    (T.original_naturality θ X) (T.original_naturality θ Y) S

end LocalizationObjects
end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
