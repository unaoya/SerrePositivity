module


public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
概要：閉対称モノイダル圏でテンソルと内部 Hom を交換する自然な射。
方針：二つの左因子を交換して評価し、curry する。
規約：同型とは主張しない。任意の閉 braided 圏で構成する。
使われ方：BF 1978 §2、HTT A.3.3。内部 Hom を各段に施した列の構造射。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.HomTensorStrength
end SerrePositivity.KST.Spectra.HomTensorStrength
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength
open _root_.SerrePositivity.KST.Spectra.HomTensorStrength

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：三重テンソルの最初の二因子を交換する同型。
方針：結合子、braiding、結合子を順に使う。
規約：括弧は右結合で入出力をそろえる。
使われ方：HTT A.3.3、BF 1978 §2。評価前の因子の順序。 -/
def exchange (A K Z : C) : A ⊗ (K ⊗ Z) ≅ K ⊗ (A ⊗ Z) :=
  (α_ A K Z).symm ≪≫ ((tensorRight Z).mapIso (β_ A K)) ≪≫ α_ K A Z

/-- 概要：因子交換は最初の因子について自然。
方針：結合子と braiding の自然性を順に使う。
規約：K と Z は固定する。
使われ方：HTT A.3.3、BF 1978 §2。内部 Hom の源の制限との整合性。 -/
@[reassoc]
theorem exchange_natural_left {A B : C} (i : A ⟶ B) (K Z : C) :
    i ▷ (K ⊗ Z) ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange B K Z).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K Z).hom ≫ K ◁ (i ▷ Z) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor, Category.assoc]
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
    associator_naturality_middle]

/-- 概要：因子交換は最後の因子について自然。
方針：結合子の自然性とテンソルの交換則を使う。
規約：A と K は固定する。
使われ方：HTT A.3.3、BF 1978 §2。内部 Hom の標的の自然性。 -/
@[reassoc]
theorem exchange_natural_right (A K : C) {Z W : C} (f : Z ⟶ W) :
    A ◁ (K ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K W).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K Z).hom ≫ K ◁ (A ◁ f) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

variable [MonoidalClosed C]

/-- 概要：左テンソルから内部 Hom の中の左テンソルへの自然な射。
方針：因子交換の後で内部 Hom を評価して curry する。
規約：K ⊗ Hom(A,Y) から Hom(A,K ⊗ Y) への射。
使われ方：BF 1978 §2、HTT A.3.3。path 列の suspension 構造。 -/
def map (K A Y : C) : K ⊗ (ihom A).obj Y ⟶ (ihom A).obj (K ⊗ Y) :=
  curry ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K ((ihom A).obj Y)).hom ≫ K ◁ (ihom.ev A).app Y)

/-- 概要：テンソルと内部 Hom の交換射の評価式。
方針：curry と uncurry の逆関係を使う。
規約：全て C の射の厳密な等式。
使われ方：HTT A.3.3、BF 1978 §2。構造射の可換式。 -/
@[reassoc]
theorem evaluation (K A Y : C) :
    A ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A Y ≫ (ihom.ev A).app (K ⊗ Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange A K ((ihom A).obj Y)).hom ≫ K ◁ (ihom.ev A).app Y :=
  uncurry_curry _

/-- 概要：テンソルと内部 Hom の交換は内部 Hom の源の制限と可換。
方針：uncurry して、源の自然性と因子交換の自然性を使う。
規約：i の単射性は不要。
使われ方：BF 1978 §2、HTT A.3.3。path の端点評価と構造射の可換性。 -/
@[reassoc]
theorem natural_pre (K : C) {A B : C} (i : A ⟶ B) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K B Y ≫ (MonoidalClosed.pre i).app (K ⊗ Y) =
      K ◁ (MonoidalClosed.pre i).app Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A Y := by
  apply uncurry_injective
  rw [uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_left, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc, ← whiskerLeft_comp, ← whiskerLeft_comp,
    MonoidalClosed.id_tensor_pre_app_comp_ev]

/-- 概要：テンソルと内部 Hom の交換は標的の射と可換。
方針：uncurry し、評価と因子交換の自然性を使う。
規約：標的の射への条件は不要。
使われ方：BF 1978 §2、HTT A.3.3。path 列の射の構造条件。 -/
@[reassoc]
theorem natural_post (K A : C) {Y Z : C} (p : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A Y ≫ (ihom A).map (K ◁ p) = K ◁ (ihom A).map p ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K A Z := by
  apply uncurry_injective
  rw [uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc, Category.assoc, ← whiskerLeft_comp,
    ← whiskerLeft_comp]
  have h : A ◁ (ihom A).map p ≫ (ihom.ev A).app Z = (ihom.ev A).app Y ≫ p :=
    (ihom.ev A).naturality p
  rw [h]

omit [BraidedCategory C] in
/-- 概要：単位からの内部 Hom の標準同型は左単位子を外した評価射。
方針：随伴間の mates と恒等随伴の counit の計算式を使う。
規約：閉構造から定まる標準の unitIsoSelf について述べる。
使われ方：HTT A.3.3、BF 1978 §2。端点評価と suspension の比較。 -/
theorem unit_evaluation (Y : C) :
    (MonoidalClosed.unitIsoSelf (X := Y)).hom =
      (λ_ ((ihom (𝟙_ C)).obj Y)).inv ≫ (ihom.ev (𝟙_ C)).app Y := by
  exact conjugateEquiv_adjunction_id (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).inv Y

omit [MonoidalClosed C] in
/-- 概要：単位因子を交換してから単位子を適用すると左単位子。
方針：単位との braiding を単位子で表し、モノイダル整合性を使う。
規約：交換される最初の因子が単位の場合。
使われ方：HTT A.3.3、BF 1978 §2。単位からの Hom の交換式。 -/
@[reassoc]
theorem exchange_unit (K Z : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (𝟙_ C) K Z).hom ≫ K ◁ (λ_ Z).hom = (λ_ (K ⊗ Z)).hom := by
  have h : (β_ (𝟙_ C) K).hom = (λ_ K).hom ≫ (ρ_ K).inv := by
    rw [← braiding_rightUnitor K, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorRight,
    Functor.flip, curriedTensor, h, comp_whiskerRight, Category.assoc]
  monoidal

/-- 概要：単位からの内部 Hom ではテンソル交換は標準同型と可換。
方針：標準同型を評価で表し、単位との交換式を使う。
規約：通常の単位同型を通した厳密な等式。
使われ方：BF 1978 §2、HTT A.3.3。path の端点評価の構造条件。 -/
@[reassoc]
theorem map_unit (K Y : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map K (𝟙_ C) Y ≫ (MonoidalClosed.unitIsoSelf (X := K ⊗ Y)).hom =
      K ◁ (MonoidalClosed.unitIsoSelf (X := Y)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation, leftUnitor_inv_naturality_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  have h : (λ_ (K ⊗ (ihom (𝟙_ C)).obj Y)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange (𝟙_ C) K ((ihom (𝟙_ C)).obj Y)).hom =
        K ◁ (λ_ ((ihom (𝟙_ C)).obj Y)).inv := by
    apply (cancel_mono (K ◁ (λ_ ((ihom (𝟙_ C)).obj Y)).hom)).mp
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_unit, Iso.inv_hom_id]
    rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
  rw [← Category.assoc, h, whiskerLeft_comp]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
