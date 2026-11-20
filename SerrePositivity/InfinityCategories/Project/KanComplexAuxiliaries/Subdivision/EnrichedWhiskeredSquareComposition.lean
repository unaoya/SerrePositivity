module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterUnits
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
概要：通常射を境界とする全 Hom パラメータの厳密可換正方形の合成。
方針：元の境界を豊穣単位パラメータで表し、既存の全パラメータ正方形の合成を使う。
規約：成分や頂点だけの可換性へ弱めない。
使われ方：相対 BF の左右境界を同時に保つ全 Hom の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra
variable (V : Type u) [Category.{v} V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type w} [Category C] [EnrichedOrdinaryCategory V C]

/-- 概要：通常の境界射の制限条件を、同じ豊穣単位パラメータの正方形へ移す。
方針：左右の単位子と豊穣 whiskering の定義を打ち消す。
規約：任意の全パラメータの射の等式。
使われ方：通常の指定境界を保つ全 Hom の合成。 -/
lemma enriched_whiskered_square_iff {P : V} {X Y X' Y' : C}
    (ex : X' ⟶ X) (ey : Y' ⟶ Y)
    (a : P ⟶ (X ⟶[V] Y)) (b : P ⟶ (X' ⟶[V] Y')) :
    a ≫ eHomWhiskerRight V ex Y = b ≫ eHomWhiskerLeft V X' ey ↔
      (eHomEquiv V ex ⊗ₘ a) ≫ eComp V X' X Y =
        (β_ (𝟙_ V) P).hom ≫ (b ⊗ₘ eHomEquiv V ey) ≫ eComp V X' Y' Y := by
  have hp : eHomEquiv V ex ▷ (X ⟶[V] Y) ≫ eComp V X' X Y =
      (λ_ (X ⟶[V] Y)).hom ≫ eHomWhiskerRight V ex Y := by
    rw [eHomWhiskerRight, Iso.hom_inv_id_assoc]
  have hq : (X' ⟶[V] Y') ◁ eHomEquiv V ey ≫ eComp V X' Y' Y =
      (ρ_ (X' ⟶[V] Y')).hom ≫ eHomWhiskerLeft V X' ey := by
    rw [eHomWhiskerLeft, Iso.hom_inv_id_assoc]
  rw [tensorHom_def', Category.assoc, hp, tensorHom_def, Category.assoc, hq,
    leftUnitor_naturality_assoc, rightUnitor_naturality_assoc]
  simp only [← Category.assoc, braiding_rightUnitor]
  simpa only [Category.assoc] using (cancel_epi (λ_ P).hom).symm

/-- 概要：通常の指定境界を持つ二つの全 Hom 正方形は厳密に合成できる。
方針：同じ境界射の単位パラメータ表示へ移し、既存の豊穣正方形合成を使う。
規約：元の境界射と全パラメータを保持する。
使われ方：相対 BF 右射影を保つ豊穣合成。 -/
lemma enriched_whiskered_square_comp {P Q : V} {X Y Z X' Y' Z' : C}
    (ex : X' ⟶ X) (ey : Y' ⟶ Y) (ez : Z' ⟶ Z)
    (a : P ⟶ (X ⟶[V] Y)) (b : P ⟶ (X' ⟶[V] Y'))
    (c : Q ⟶ (Y ⟶[V] Z)) (d : Q ⟶ (Y' ⟶[V] Z'))
    (ha : a ≫ eHomWhiskerRight V ex Y = b ≫ eHomWhiskerLeft V X' ey)
    (hb : c ≫ eHomWhiskerRight V ey Z = d ≫ eHomWhiskerLeft V Y' ez) :
    (a ⊗ₘ c) ≫ eComp V X Y Z ≫ eHomWhiskerRight V ex Z =
      (b ⊗ₘ d) ≫ eComp V X' Y' Z' ≫ eHomWhiskerLeft V X' ez := by
  rw [← Category.assoc, ← Category.assoc]
  apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff V ex ez _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_comp V (eHomEquiv V ex) (eHomEquiv V ey)
    (eHomEquiv V ez) a b c d
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff V ex ey a b).mp ha)
    ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff V ey ez c d).mp hb)

/-- 概要：同じ通常の指定境界に対して二つの豊穣恒等射は厳密可換。
方針：単位パラメータの恒等正方形を元の whiskering へ戻す。
規約：元の境界射を保持する。
使われ方：両境界を保つ全 Hom の組の恒等射。 -/
lemma enriched_whiskered_square_id {X Y : C} (f : X ⟶ Y) :
    eId V Y ≫ eHomWhiskerRight V f Y = eId V X ≫ eHomWhiskerLeft V X f := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff V f f _ _).mpr
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_square_id V (eHomEquiv V f)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
