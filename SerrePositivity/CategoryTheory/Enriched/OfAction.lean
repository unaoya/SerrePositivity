module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor

/-!
# 閉じた右加群の豊穣化

## 概要
閉じた右作用から、元の通常圏を保つ豊穣圏を作る。

## 方針
写像対象の評価を二回行い、随伴で転置して合成を得る。

## 規約
合成の因子は Mathlib の図式順に置く。係数は対象の右から作用する。

## 使われ方
作用と随伴を指定した利用側が、豊穣化とそのテンソル・余テンソルを選ぶ。
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalRightAction Opposite
open SerrePositivity.Enriched

universe u₁ v₁ u₂ v₂

variable (V : Type u₁) (M : Type u₂) [Category.{v₁} V] [Category.{v₂} M]
  [MonoidalCategory V] [MonoidalRightAction V M]

/-- 閉じた右加群は、右作用が係数ごとに余テンソル、原対象ごとに写像対象を右随伴に持つもの。
Mathlib の `MonoidalClosed` は基底自身のテンソルの閉性を指定する。
Riehl の結合・単位には右作用の整合を課す。 -/
@[cite R"10.1.3"(partial:=stronger-hyp) "結合子と単位子に右作用の整合を課す。",
  cite H"4.1.6"(partial:=component) "右加群のうち二つの随伴を持つ場合。",
  cite H"4.1.12"(partial:=special) "二つのパラメータ付き随伴を束ねる。"]
class ClosedModule where
  /-- 係数に反変な余テンソル。 -/
  cotensor : Vᵒᵖ ⥤ M ⥤ M
  /-- 原対象に反変、終対象に共変な写像対象。 -/
  mapping : Mᵒᵖ ⥤ M ⥤ V
  /-- 係数を固定した余テンソル随伴。 -/
  cotensorAdj : curriedAction V M ⊣₂ cotensor
  /-- 原対象を固定した写像対象随伴。 -/
  mappingAdj : (curriedAction V M).flip ⊣₂ mapping

namespace ClosedModule

variable {M} [ClosedModule V M]

/-- 原対象と終対象を固定した写像対象。 -/
abbrev hom (X Y : M) : V := ((mapping (V := V)).obj (op X)).obj Y

/-- 評価は原対象を固定した写像対象随伴の余単位。 -/
@[cite R"10.1.4"(partial:=component) "右作用での写像対象の評価。"]
def ev (X Y : M) : X ⊙ᵣ (hom V X Y) ⟶ Y :=
  ((mappingAdj (V := V)).adj X).counit.app Y

/-- 写像随伴による転置を、右作用の記法で取る。 -/
abbrev transpose (X : M) (P : V) (Y : M) : (X ⊙ᵣ P ⟶ Y) ≃ (P ⟶ hom V X Y) :=
  ((mappingAdj (V := V)).adj X).homEquiv P Y

/-- 逆転置は係数の射を作用に入れてから評価する。 -/
lemma homEquiv_symm_eq_action_ev {P : V} {X Y : M} (f : P ⟶ hom V X Y) :
    (transpose V X P Y).symm f = X ⊴ᵣ f ≫ ev V X Y :=
  ((mappingAdj (V := V)).adj X).homEquiv_counit P Y f

/-- 評価して一致する写像対象への二射は等しい。 -/
lemma hom_ext {P : V} {X Y : M} {f g : P ⟶ hom V X Y}
    (h : X ⊴ᵣ f ≫ ev V X Y = X ⊴ᵣ g ≫ ev V X Y) : f = g := by
  apply (transpose V X P Y).symm.injective
  rw [homEquiv_symm_eq_action_ev, homEquiv_symm_eq_action_ev]
  exact h

/-- 恒等の点は右作用の単位子の転置。 -/
@[cite R"10.1.4"(partial:=component) "豊穣圏の単位。"]
def eId (X : M) : 𝟙_ V ⟶ hom V X X :=
  transpose V X (𝟙_ V) X (ρᵣ[V] X).hom

/-- 通常射は、右作用の単位子で前合成して転置すると写像対象の点になる。 -/
@[cite R"3.4.9"(partial:=component) "通常射と点の同値を右作用で与える。"]
def homEquiv (X Y : M) : (X ⟶ Y) ≃ (𝟙_ V ⟶ hom V X Y) :=
  { toFun := fun f ↦ transpose V X (𝟙_ V) Y ((ρᵣ[V] X).hom ≫ f)
    invFun := fun g ↦ (ρᵣ[V] X).inv ≫ (transpose V X (𝟙_ V) Y).symm g
    left_inv := fun f ↦ by
      dsimp only
      rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
    right_inv := fun g ↦ by
      dsimp only
      rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply] }

/-- 通常射の点を取る同値の順写像。 -/
lemma homEquiv_apply {X Y : M} (f : X ⟶ Y) :
    homEquiv V X Y f = transpose V X (𝟙_ V) Y ((ρᵣ[V] X).hom ≫ f) :=
  rfl

/-- 通常射を表す点を評価すると、作用の単位子を経由する通常射になる。 -/
@[reassoc]
lemma homEquiv_ev {X Y : M} (f : X ⟶ Y) :
    X ⊴ᵣ homEquiv V X Y f ≫ ev V X Y = (ρᵣ[V] X).hom ≫ f := by
  rw [← homEquiv_symm_eq_action_ev, homEquiv_apply]
  exact Equiv.symm_apply_apply _ _

/-- 恒等射を表す点は豊穣化の単位。 -/
@[simp]
lemma homEquiv_id (X : M) : homEquiv V X X (𝟙 X) = eId V X := by
  rw [homEquiv_apply, Category.comp_id, eId]

/-- 豊穣合成は、右作用を二段に分け、評価を二回行った射の転置。 -/
@[cite R"10.1.4"(partial:=component) "右作用で評価を並べ、合成の因子を図式順に置く。"]
def comp (X Y Z : M) : hom V X Y ⊗ hom V Y Z ⟶ (hom V X Z) :=
  transpose V X _ Z
    ((αᵣ X (hom V X Y) (hom V Y Z)).hom ≫ ev V X Y ⊵ᵣ (hom V Y Z) ≫ ev V Y Z)

/-- 合成を評価すると、作用の結合子を経由して評価を二度行う。 -/
@[reassoc]
lemma comp_ev (X Y Z : M) :
    X ⊴ᵣ comp V X Y Z ≫ ev V X Z =
      (αᵣ X (hom V X Y) (hom V Y Z)).hom ≫ ev V X Y ⊵ᵣ (hom V Y Z) ≫ ev V Y Z := by
  rw [← homEquiv_symm_eq_action_ev, comp]
  exact Equiv.symm_apply_apply _ _

/-- 通常射を第一の因子に入れた豊穣合成の評価。 -/
@[reassoc]
private lemma precomp_ev {X Y Z : M} (f : X ⟶ Y) :
    X ⊴ᵣ (homEquiv V X Y f ▷ (hom V Y Z)) ≫ X ⊴ᵣ comp V X Y Z ≫ ev V X Z =
      X ⊴ᵣ (λ_ (hom V Y Z)).hom ≫ f ⊵ᵣ (hom V Y Z) ≫ ev V Y Z := by
  rw [actionHomRight_whiskerRight_assoc, comp_ev, Iso.inv_hom_id_assoc,
    ← comp_actionHomLeft_assoc, homEquiv_ev, comp_actionHomLeft, Category.assoc,
    ← actionHom_leftUnitor_assoc]

/-- 通常射を第二の因子に入れた豊穣合成の評価。 -/
@[reassoc]
private lemma postcomp_ev {X Y Z : M} (g : Y ⟶ Z) :
    X ⊴ᵣ ((hom V X Y) ◁ homEquiv V Y Z g) ≫ X ⊴ᵣ comp V X Y Z ≫ ev V X Z =
      X ⊴ᵣ (ρ_ (hom V X Y)).hom ≫ ev V X Y ≫ g := by
  simp only [whiskerRight_actionHomLeft, Category.assoc, comp_ev, Iso.inv_hom_id_assoc]
  rw [action_exchange_assoc, homEquiv_ev, ← actionUnitIso_hom_naturality_assoc,
    ← actionHom_rightUnitor_assoc]

/-- 豊穣合成で通常射を先に適用すると、写像対象の反変関手性になる。 -/
@[reassoc]
lemma homEquiv_whiskerRight_comp {X Y : M} (f : X ⟶ Y) (Z : M) :
    (λ_ (hom V Y Z)).inv ≫ homEquiv V X Y f ▷ (hom V Y Z) ≫ comp V X Y Z =
      ((mapping (V := V)).map f.op).app Z := by
  apply hom_ext V
  simp only [actionHomRight_comp, Category.assoc, precomp_ev, actionHomRight_inv_hom_assoc]
  rw [← homEquiv_symm_eq_action_ev]
  simpa only [ParametrizedAdjunction.homEquiv_eq, Category.id_comp, Adjunction.homEquiv_symm_id,
    Functor.flip_map_app, MonoidalRightAction.curriedAction_obj_map, ev] using!
    ((mappingAdj (V := V) (M := M)).homEquiv_symm_naturality_one f (𝟙 (hom V Y Z))).symm

/-- 豊穣合成で通常射を後に適用すると、写像対象の共変関手性になる。 -/
@[reassoc]
lemma whiskerLeft_homEquiv_comp (X : M) {Y Z : M} (g : Y ⟶ Z) :
    (ρ_ (hom V X Y)).inv ≫ (hom V X Y) ◁ homEquiv V Y Z g ≫ comp V X Y Z =
      ((mapping (V := V)).obj (op X)).map g := by
  apply hom_ext V
  simp only [actionHomRight_comp, Category.assoc, postcomp_ev, actionHomRight_inv_hom_assoc]
  exact (((mappingAdj (V := V)).adj X).counit.naturality g).symm

/-- 四つの対象の合成を評価し、右作用の四重結合図式を使う。 -/
private lemma comp_assoc_hom (W X Y Z : M) :
    comp V W X Y ▷ (hom V Y Z) ≫ comp V W Y Z =
      (α_ (hom V W X) (hom V X Y) (hom V Y Z)).hom ≫
        (hom V W X) ◁ comp V X Y Z ≫ comp V W X Z := by
  apply hom_ext V
  simp only [actionHomRight_comp, Category.assoc, comp_ev]
  rw [actionHomRight_whiskerRight_assoc, Iso.inv_hom_id_assoc, ← comp_actionHomLeft_assoc,
    comp_ev, comp_actionHomLeft, comp_actionHomLeft]
  simp only [whiskerRight_actionHomLeft, Category.assoc, Iso.inv_hom_id_assoc]
  rw [action_exchange_assoc, comp_ev, actionHomLeft_tensor_assoc]
  simp only [Iso.inv_hom_id_assoc, actionHom_associator_assoc]

/-- 通常射の合成を転置すると、通常射を表す点の豊穣合成になる。 -/
@[cite R"3.4.5"(partial:=component) "通常射の点と豊穣合成の両立。"]
lemma homEquiv_comp {X Y Z : M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homEquiv V X Z (f ≫ g) = (λ_ (𝟙_ V)).inv ≫ (homEquiv V X Y f ⊗ₘ homEquiv V Y Z g) ≫
      comp V X Y Z := by
  rw [leftUnitor_inv_comp_tensorHom_assoc, homEquiv_whiskerRight_comp,
    homEquiv_apply, homEquiv_apply, ← Category.assoc, actionUnitIso_hom_naturality f,
    Category.assoc]
  exact (mappingAdj (V := V) (M := M)).homEquiv_naturality_one f _

/-- 閉じた右加群は、元の通常圏を保つ豊穣圏を与える。 -/
@[cite R"10.1.4"(partial:=component) "右作用から通常圏を保つ豊穣化。", instance_reducible,
  simps id comp homEquiv]
def enrichedOrdinaryCategory : EnrichedOrdinaryCategory V M where
  Hom := hom V
  id := eId V
  comp := comp V
  id_comp X Y := by
    rw [← homEquiv_id, homEquiv_whiskerRight_comp, op_id, Functor.map_id, NatTrans.id_app]
  comp_id X Y := by
    rw [← homEquiv_id, whiskerLeft_homEquiv_comp, Functor.map_id]
  assoc W X Y Z := by
    rw [comp_assoc_hom, Iso.inv_hom_id_assoc]
  homEquiv := homEquiv V _ _
  homEquiv_id := homEquiv_id V
  homEquiv_comp := homEquiv_comp V

/-- 通常豊穣化の Hom 関手と写像対象の関手の自然同型。 -/
@[cite R"10.1.4"(partial:=component) "所与の写像対象の二変数自然性を保持する。"]
def eHomFunctorIso :
    @eHomFunctor V _ _ M _ (enrichedOrdinaryCategory V) ≅ mapping :=
  NatIso.ofComponents (fun X ↦
    NatIso.ofComponents (fun Y ↦ Iso.refl (hom V X.unop Y)) (fun {Y Z} g ↦ by
      have h := whiskerLeft_homEquiv_comp V X.unop g
      simpa only [eHomFunctor_obj_map, Iso.refl_hom, eHomWhiskerLeft, CategoryTheory.eComp,
        CategoryTheory.eHomEquiv, enrichedOrdinaryCategory_comp, enrichedOrdinaryCategory_homEquiv,
        op_unop] using! (Category.comp_id _).trans (h.trans (Category.id_comp _).symm)))
    (fun {X X'} f ↦ by
      apply NatTrans.ext
      funext Y
      have h := homEquiv_whiskerRight_comp V f.unop Y
      simpa only [eHomFunctor_map_app, NatTrans.comp_app, NatIso.ofComponents_hom_app,
        Iso.refl_hom, eHomWhiskerRight, CategoryTheory.eComp, CategoryTheory.eHomEquiv,
        enrichedOrdinaryCategory_comp, enrichedOrdinaryCategory_homEquiv] using!
        (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

/-- 写像対象への自然同型の順射は、各対象対で恒等射。 -/
@[reassoc (attr := simp)]
lemma eHomFunctorIso_hom_app_app (X : Mᵒᵖ) (Y : M) :
    ((eHomFunctorIso V).hom.app X).app Y = 𝟙 (hom V X.unop Y) := rfl

/-- 写像対象への自然同型の逆射は、各対象対で恒等射。 -/
@[reassoc (attr := simp)]
lemma eHomFunctorIso_inv_app_app (X : Mᵒᵖ) (Y : M) :
    ((eHomFunctorIso V).inv.app X).app Y = 𝟙 (hom V X.unop Y) := rfl

/-- 右作用と余テンソル随伴を保ち、写像随伴を Hom の自然同型に沿って移す。 -/
@[cite R"10.1.4"(partial:=component) "元の二つの通常随伴を保持する。",
  simps tensor cotensor tensorCotensor tensorHom]
def tensorCotensor : @TensorCotensor V _ _ M _ (enrichedOrdinaryCategory V) :=
  -- 写像随伴の終域に、戻り型と同じ選択の豊穣化を渡す。
  letI := enrichedOrdinaryCategory V (M := M)
  { tensor := curriedAction V M
    cotensor := ClosedModule.cotensor
    tensorCotensor := cotensorAdj
    tensorHom := SerrePositivity.ParametrizedAdjunctionTransport.right
      mappingAdj (eHomFunctorIso V (M := M)).symm }

end ClosedModule

namespace MonoidalClosed

/-- 自己右作用を持つ閉モノイダル圏から閉加群を得る。
写像随伴は左テンソルの閉随伴そのもので、組紐は右テンソルを左テンソルに比べる
余テンソル随伴の欄だけに使う。 -/
@[cite R"3.7.5"(partial:=component) "自己作用の閉性を二つの随伴で与える。", instance_reducible,
  simps cotensor mapping cotensorAdj mappingAdj]
def closedModuleSelf (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
    [BraidedCategory V] [MonoidalClosed V] :
    @ClosedModule V V _ _ _ (selfRightAction V) where
  cotensor := internalHom
  mapping := internalHom
  cotensorAdj := SerrePositivity.ParametrizedAdjunctionTransport.left
    internalHomAdjunction₂ (BraidedCategory.curriedBraidingNatIso V)
  mappingAdj := internalHomAdjunction₂

end MonoidalClosed
end CategoryTheory
end
