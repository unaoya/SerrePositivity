module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.CategoryTheory.Enriched.BaseChange
public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor

/-!
# 閉じた加群の豊穣化

作用と二つの随伴から、もとの通常圏を保つ豊穣化を作る。評価の計算は文献の後射を
左に置く順で行い、得られた合成を Mathlib の図式順に移す。
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory BraidedCategory Opposite
open SerrePositivity.Enriched

universe u v w z

variable (V : Type u) (M : Type w) [Category.{v} V] [Category.{z} M] [MonoidalCategory V]
  [a : MonoidalLeftAction V M]

/-- 閉じた左加群は、Mathlib の整合つき左作用に余テンソル随伴と写像対象随伴を加えたもの。
Mathlib の `MonoidalClosed` は基底の自己作用についてテンソルの右随伴を指定する。
Hovey の右作用は左に読み替え、Riehl の結合と単位には作用の整合を課す。 -/
@[cite R"10.1.3"(partial:=stronger-hyp) "結合子と単位子に左作用の整合を課す。",
  cite H"4.1.6"(partial:=component) "右作用を左に読み替え、二つの随伴を持つ場合。",
  cite H"4.1.12"(partial:=special) "左作用について二つのパラメータ付き随伴を束ねる。"]
class ClosedModule where
  /-- 係数に反変な余テンソル。 -/
  cotensor : Vᵒᵖ ⥤ M ⥤ M
  /-- 二変数の写像対象。 -/
  mapping : Mᵒᵖ ⥤ M ⥤ V
  /-- 係数を固定した余テンソル随伴。 -/
  cotensorAdj : MonoidalLeftAction.curriedAction V M ⊣₂ cotensor
  /-- 原対象を固定した写像対象随伴。 -/
  mappingAdj : (MonoidalLeftAction.curriedAction V M).flip ⊣₂ mapping

variable {V M}

namespace ClosedModule

/-- 原対象と終対象を固定した写像対象。 -/
@[cite R"10.1.3"(partial:=component) "二変数随伴の写像対象の値。"]
abbrev hom (L : ClosedModule V M) (X Y : M) : V := (L.mapping.obj (op X)).obj Y

end ClosedModule

variable (L : ClosedModule V M)

local notation "T" => MonoidalLeftAction.curriedAction V M

/-- 評価は、原対象を固定した写像対象随伴の余単位。 -/
@[cite R"10.1.4"(partial:=component) "合成に使う写像対象随伴の評価。"]
def actionEvaluation (X Y : M) : ((T).obj (L.hom X Y)).obj X ⟶ Y :=
  (L.mappingAdj.adj X).counit.app Y

/-- 写像対象の単位は、作用の左単位子の転置。 -/
@[cite R"10.1.4"(partial:=component) "閉じた加群から作る豊穣圏の単位。"]
def actionUnit (X : M) : 𝟙_ V ⟶ L.hom X X :=
  (L.mappingAdj.adj X).homEquiv _ X
    ((@MonoidalLeftAction.actionUnitNatIso V M _ _ _ a).hom.app X)

/-- 通常射を作用単位子で前合成して転置すると、写像対象の点を得る。 -/
@[cite R"3.4.9"(partial:=component) "自己作用の単位点の式を閉じた加群に適用する。"]
def actionHomEquiv (X Y : M) : (X ⟶ Y) ≃ (𝟙_ V ⟶ L.hom X Y) :=
  SerrePositivity.AdjunctionHomLaws.comparisonHomEquiv (L.mappingAdj.adj X)
    ((@MonoidalLeftAction.actionUnitNatIso V M _ _ _ a).app X) Y

local notation "Assoc" => @MonoidalLeftAction.actionAssocNatIso V M _ _ _ a
local notation "A" => fun P Q X => Iso.app (Iso.app (Iso.app (Assoc) P) Q) X
local notation "Unit" => @MonoidalLeftAction.actionUnitNatIso V M _ _ _ a
local notation "U" => fun X => Iso.app (Unit) X

/-- 写像対象の二つの評価を合成する。文献順で、後から適用する射が左に来る。 -/
@[cite R"3.3.8"(partial:=component) "自己作用の評価式を左加群の評価に適用する。"]
def compositionEvaluation (X Y Z : M) :
    ((T).obj (L.hom Y Z ⊗ L.hom X Y)).obj X ⟶ Z :=
  (A (L.hom Y Z) (L.hom X Y) X).hom ≫
    ((T).obj (L.hom Y Z)).map (actionEvaluation L X Y) ≫ actionEvaluation L Y Z

/-- 後から適用する射を左に置く合成は、二つの評価の転置。 -/
@[cite R"10.1.4"(partial:=component) "豊穣合成の文献順での式。"]
def reverseComposition (X Y Z : M) : L.hom Y Z ⊗ L.hom X Y ⟶ L.hom X Z :=
  (L.mappingAdj.adj X).homEquiv _ Z (compositionEvaluation L X Y Z)

/-- 写像対象への射を作用に入れてから評価することは逆転置に等しい。 -/
private lemma untranspose_eval {P : V} {X Y : M} (f : P ⟶ L.hom X Y) :
    ((L.mappingAdj.adj X).homEquiv P Y).symm f =
      ((T).map f).app X ≫ actionEvaluation L X Y :=
  (L.mappingAdj.adj X).homEquiv_counit P Y f

/-- 文献順の合成の評価を、二つの評価へ戻す補助。 -/
@[reassoc]
private lemma reverseComposition_eval (X Y Z : M) :
    ((T).map (reverseComposition L X Y Z)).app X ≫ actionEvaluation L X Z =
      compositionEvaluation L X Y Z := by
  rw [← untranspose_eval, reverseComposition, Equiv.symm_apply_apply]

/-- 単位点に対応する射の評価は、作用単位を経由した通常射。 -/
@[reassoc]
private lemma actionHomEquiv_eval {X Y : M} (f : X ⟶ Y) :
    ((T).map (actionHomEquiv L X Y f)).app X ≫ actionEvaluation L X Y =
      (U X).hom ≫ f :=
  SerrePositivity.AdjunctionHomLaws.comparison_evaluation (L.mappingAdj.adj X)
    ((@MonoidalLeftAction.actionUnitNatIso V M _ _ _ a).app X) f

/-- 恒等射の点は、写像対象の単位。 -/
@[simp]
lemma actionHomEquiv_id (X : M) : actionHomEquiv L X X (𝟙 X) = actionUnit L X := by
  rw [actionHomEquiv, SerrePositivity.AdjunctionHomLaws.comparisonHomEquiv_apply]
  exact congrArg (fun f ↦ (L.mappingAdj.adj X).homEquiv (𝟙_ V) X f)
    (Category.comp_id (U X).hom)

/-- 評価で二つの写像対象への射が一致すれば、逆転置の単射性により元の射も一致する。 -/
private lemma eval_injective {P : V} {X Y : M} {f g : P ⟶ L.hom X Y}
    (h : ((T).map f).app X ≫ actionEvaluation L X Y =
      ((T).map g).app X ≫ actionEvaluation L X Y) : f = g := by
  apply ((L.mappingAdj.adj X).homEquiv P Y).symm.injective
  simpa only [untranspose_eval] using h

/-- 結合子は、左の係数に射を作用させても自然。 -/
@[reassoc]
private lemma assoc_map_left {P P' : V} (f : P ⟶ P') (Q : V) (X : M) :
    ((T).map (f ▷ Q)).app X ≫ (A P' Q X).hom =
      (A P Q X).hom ≫ ((T).map f).app (((T).obj Q).obj X) := by
  apply (Iso.eq_comp_inv (A P' Q X)).mp
  rw [Category.assoc]
  exact @MonoidalLeftAction.whiskerRight_actionHomLeft V M _ _ _ a P P' Q f X

/-- 結合子は、右の係数に射を作用させても自然。 -/
@[reassoc]
private lemma assoc_map_right (P : V) {Q Q' : V} (f : Q ⟶ Q') (X : M) :
    ((T).map (P ◁ f)).app X ≫ (A P Q' X).hom =
      (A P Q X).hom ≫ ((T).obj P).map (((T).map f).app X) := by
  apply (Iso.eq_comp_inv (A P Q' X)).mp
  rw [Category.assoc]
  exact @MonoidalLeftAction.whiskerLeft_actionHomLeft V M _ _ _ a P Q Q' f X

/-- 作用の単位子の自然性をカリー化した作用で読む。 -/
@[reassoc]
private lemma unit_map {X Y : M} (f : X ⟶ Y) :
    ((T).obj (𝟙_ V)).map f ≫ (U Y).hom = (U X).hom ≫ f :=
  (Unit).hom.naturality f

/-- 作用の左単位図式をカリー化した作用で読む。 -/
@[reassoc]
private lemma action_leftUnitor (P : V) (X : M) :
    (A (𝟙_ V) P X).hom ≫ (U (((T).obj P).obj X)).hom =
      ((T).map (λ_ P).hom).app X :=
  (@MonoidalLeftAction.leftUnitor_actionHom V M _ _ _ a P X).symm

/-- 作用の右単位図式をカリー化した作用で読む。 -/
@[reassoc]
private lemma action_rightUnitor (P : V) (X : M) :
    (A P (𝟙_ V) X).hom ≫ ((T).obj P).map (U X).hom = ((T).map (ρ_ P).hom).app X :=
  (@MonoidalLeftAction.rightUnitor_actionHom V M _ _ _ a P X).symm

/-- 二つの係数を固定した作用結合子の対象変数に関する自然性。 -/
@[reassoc]
private lemma action_assoc_naturality (P Q : V) {X Y : M} (f : X ⟶ Y) :
    ((T).obj (P ⊗ Q)).map f ≫ (A P Q Y).hom =
      (A P Q X).hom ≫ ((T).obj P).map (((T).obj Q).map f) :=
  (((Assoc).hom.app P).app Q).naturality f

/-- 作用の四重結合をカリー化した作用で読む。 -/
@[reassoc]
private lemma action_pentagon (P Q R : V) (X : M) :
    ((T).map (α_ P Q R).hom).app X ≫ (A P (Q ⊗ R) X).hom ≫
      ((T).obj P).map (A Q R X).hom =
        (A (P ⊗ Q) R X).hom ≫ (A P Q (((T).obj R).obj X)).hom :=
  @MonoidalLeftAction.associator_actionHom V M _ _ _ a P Q R X

/-- 文献順の二つの評価で、後から適用する射が通常射の場合の計算。 -/
@[reassoc]
private lemma reverseComposition_post_eval {X Y Z : M} (g : Y ⟶ Z) :
    ((T).map (actionHomEquiv L Y Z g ▷ L.hom X Y)).app X ≫
      compositionEvaluation L X Y Z =
        ((T).map (λ_ (L.hom X Y)).hom).app X ≫ actionEvaluation L X Y ≫ g := by
  rw [compositionEvaluation, assoc_map_left_assoc,
    ← ((T).map (actionHomEquiv L Y Z g)).naturality_assoc,
    actionHomEquiv_eval, unit_map_assoc, action_leftUnitor_assoc]

/-- 文献順の二つの評価で、先に適用する射が通常射の場合の計算。 -/
@[reassoc]
private lemma reverseComposition_pre_eval {X Y Z : M} (f : X ⟶ Y) :
    ((T).map (L.hom Y Z ◁ actionHomEquiv L X Y f)).app X ≫
      compositionEvaluation L X Y Z =
        ((T).map (ρ_ (L.hom Y Z)).hom).app X ≫
          ((T).obj (L.hom Y Z)).map f ≫ actionEvaluation L Y Z := by
  rw [compositionEvaluation, assoc_map_right_assoc, ← Functor.map_comp_assoc,
    actionHomEquiv_eval, Functor.map_comp, Category.assoc, action_rightUnitor_assoc]

/-- 文献順の合成で、後から適用する射を単位に取る。 -/
private lemma reverseComposition_left_unit (X Y : M) :
    (actionUnit L Y ⊗ₘ 𝟙 (L.hom X Y)) ≫ reverseComposition L X Y Y = (λ_ _).hom := by
  apply eval_injective L
  rw [← actionHomEquiv_id, tensorHom_id, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, reverseComposition_eval, reverseComposition_post_eval, Category.comp_id]

/-- 文献順の合成で、先に適用する射を単位に取る。 -/
private lemma reverseComposition_right_unit (X Y : M) :
    (𝟙 (L.hom X Y) ⊗ₘ actionUnit L X) ≫ reverseComposition L X X Y = (ρ_ _).hom := by
  apply eval_injective L
  rw [← actionHomEquiv_id, id_tensorHom, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, reverseComposition_eval, reverseComposition_pre_eval, Functor.map_id,
    Category.id_comp]

/-- 文献順の合成は作用の四重結合図式によって結合的になる。 -/
private lemma reverseComposition_assoc (W X Y Z : M) :
    (reverseComposition L X Y Z ⊗ₘ 𝟙 (L.hom W X)) ≫ reverseComposition L W X Z =
      (α_ (L.hom Y Z) (L.hom X Y) (L.hom W X)).hom ≫
        (𝟙 (L.hom Y Z) ⊗ₘ reverseComposition L W X Y) ≫ reverseComposition L W Y Z := by
  apply eval_injective L
  simp only [tensorHom_id, id_tensorHom, Functor.map_comp, NatTrans.comp_app, Category.assoc,
    reverseComposition_eval, compositionEvaluation]
  rw [assoc_map_left_assoc, assoc_map_right_assoc]
  rw [← ((T).map (reverseComposition L X Y Z)).naturality_assoc,
    reverseComposition_eval, compositionEvaluation]
  rw [← Functor.map_comp_assoc, reverseComposition_eval, compositionEvaluation]
  simp only [Functor.map_comp, Category.assoc]
  rw [action_assoc_naturality_assoc, ← action_pentagon_assoc]

/-- 文献順で二つの通常射に対応する点を合成すると、通常射の合成に対応する。 -/
private lemma reverseComposition_points {X Y Z : M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (λ_ (𝟙_ V)).inv ≫ (actionHomEquiv L Y Z g ⊗ₘ actionHomEquiv L X Y f) ≫
        reverseComposition L X Y Z =
      actionHomEquiv L X Z (f ≫ g) := by
  apply eval_injective L
  simp only [tensorHom_def', Functor.map_comp, NatTrans.comp_app, Category.assoc,
    reverseComposition_eval]
  rw [reverseComposition_post_eval, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Category.assoc, leftUnitor_naturality, Iso.inv_hom_id_assoc,
    actionHomEquiv_eval_assoc, actionHomEquiv_eval]

variable [BraidedCategory V]

open SerrePositivity.ReverseComposition

/-- 豊穣合成は文献順の評価を転置し、組紐で Mathlib の図式順に直したもの。 -/
@[cite R"10.1.4"(partial:=component) "豊穣合成。原典と因子の順を逆にする。"]
def actionComposition (L : ClosedModule V M) (X Y Z : M) :
    L.hom X Y ⊗ L.hom Y Z ⟶ L.hom X Z :=
  reverse (reverseComposition L X Y Z)

/-- 閉じた加群上の豊穣構造。合成は Mathlib の図式順。 -/
@[instance_reducible]
def actionEnrichedCategory (L : ClosedModule V M) : EnrichedCategory V M :=
  SerrePositivity.ReverseComposition.enrichedCategory M
    L.hom (actionUnit L) (reverseComposition L)
    (by exact reverseComposition_left_unit L) (by exact reverseComposition_right_unit L)
    (by exact reverseComposition_assoc L)

/-- 閉じた加群から作る図式順での豊穣合成の結合則。 -/
@[cite R"10.1.4"(partial:=component) "結合律。文献と因子順が逆で、作用の整合を仮定する。"]
lemma actionComposition_assoc (L : ClosedModule V M) (W X Y Z : M) :
    (actionComposition L W X Y ▷ L.hom Y Z) ≫ actionComposition L W Y Z =
      (α_ (L.hom W X) (L.hom X Y) (L.hom Y Z)).hom ≫
        (L.hom W X ◁ actionComposition L X Y Z) ≫ actionComposition L W X Z := by
  have h := (actionEnrichedCategory L).assoc W X Y Z
  apply (cancel_epi (α_ (L.hom W X) (L.hom X Y) (L.hom Y Z)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact h

/-- 閉じた左加群は元の通常圏を保つ豊穣圏になる。合成は Mathlib の図式順。 -/
@[cite R"10.1.4"(partial:=component) "通常圏を保つ豊穣化のみ。作用の整合を仮定する。",
  instance_reducible]
def ofAction (L : ClosedModule V M) : EnrichedOrdinaryCategory V M where
  toEnrichedCategory := actionEnrichedCategory L
  homEquiv := actionHomEquiv L _ _
  homEquiv_id := actionHomEquiv_id L
  homEquiv_comp f g :=
    by exact (points _ _ _ _ (reverseComposition_points L f g)).symm

/-- 作用から作った豊穣圏の Hom は、選んだ写像対象。 -/
lemma ofAction_hom (X Y : M) :
    @EnrichedCategory.Hom V _ _ M (ofAction L).toEnrichedCategory X Y = L.hom X Y :=
  rfl

/-- 作用から作った豊穣圏の単位は、作用単位子の転置。 -/
lemma ofAction_id (X : M) : @eId V _ _ M (ofAction L).toEnrichedCategory X = actionUnit L X :=
  rfl

/-- 作用から作った豊穣圏の合成は、図式順にした二つの評価の転置。 -/
lemma ofAction_comp (X Y Z : M) :
    @eComp V _ _ M (ofAction L).toEnrichedCategory X Y Z = actionComposition L X Y Z :=
  rfl

/-- 通常射の点は、作用単位子で前合成した射の転置。 -/
lemma ofAction_homEquiv_apply {X Y : M} (f : X ⟶ Y) :
    @eHomEquiv V _ _ M _ (ofAction L) X Y f = actionHomEquiv L X Y f :=
  rfl

/-- 通常射による後合成は、写像対象の共変な関手性に一致する。 -/
private lemma ofAction_whiskerLeft (X : M) {Y Z : M} (g : Y ⟶ Z) :
    @eHomWhiskerLeft V _ _ M _ (ofAction L) X Y Z g = (L.mapping.obj (op X)).map g := by
  -- 定義を開いて、図式順の合成を文献順の評価に戻す。
  change (ρ_ (L.hom X Y)).inv ≫ L.hom X Y ◁ actionHomEquiv L Y Z g ≫
    reverse (reverseComposition L X Y Z) = _
  rw [reverse, braiding_naturality_right_assoc, ← Category.assoc, rightUnitor_inv_braiding]
  apply eval_injective L (X := X) (Y := Z)
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, reverseComposition_eval]
  rw [reverseComposition_post_eval, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, NatTrans.id_app, Category.id_comp]
  exact ((L.mappingAdj.adj X).counit.naturality g).symm

/-- 通常射による前合成は、写像対象の反変な関手性に一致する。 -/
private lemma ofAction_whiskerRight {X Y : M} (f : X ⟶ Y) (Z : M) :
    @eHomWhiskerRight V _ _ M _ (ofAction L) X Y f Z = (L.mapping.map f.op).app Z := by
  -- 定義を開いて、図式順の合成を文献順の評価に戻す。
  change (λ_ (L.hom Y Z)).inv ≫ actionHomEquiv L X Y f ▷ L.hom Y Z ≫
    reverse (reverseComposition L X Y Z) = _
  rw [reverse, braiding_naturality_left_assoc, ← Category.assoc, leftUnitor_inv_braiding]
  apply eval_injective L (X := X) (Y := Z)
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc, reverseComposition_eval]
  rw [reverseComposition_pre_eval, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, NatTrans.id_app, Category.id_comp, ← untranspose_eval]
  apply ((L.mappingAdj.adj X).homEquiv (L.hom Y Z) Z).eq_symm_apply.mpr
  have h := L.mappingAdj.homEquiv_naturality_one (X₁ := X) (Y₁ := Y) (X₂ := L.hom Y Z) f
    (actionEvaluation L Y Z)
  have he : L.mappingAdj.homEquiv (X₁ := Y) (X₂ := L.hom Y Z) (actionEvaluation L Y Z) = 𝟙 _ :=
    ((L.mappingAdj.adj Y).homEquiv _ Z).eq_symm_apply.mp
      ((L.mappingAdj.adj Y).homEquiv_symm_id Z).symm
  rw [he, Category.id_comp] at h
  exact h

/-- 通常豊穣化の Hom 関手は、閉じた加群が指定する写像対象関手に自然同型。 -/
@[cite R"10.1.4"(partial:=component) "与えられた写像対象を保持する。"]
def ofActionHomIso (L : ClosedModule V M) :
    @eHomFunctor V _ _ M _ (ofAction L) ≅ L.mapping :=
  NatIso.ofComponents (fun X ↦
    NatIso.ofComponents (fun Y ↦ Iso.refl (L.hom X.unop Y)) (fun {Y Z} f ↦ by
      -- 自然性の方程式の Hom の恒等成分を明示する。
      change @eHomWhiskerLeft V _ _ M _ (ofAction L) X.unop Y Z f ≫ 𝟙 _ =
        𝟙 _ ≫ (L.mapping.obj X).map f
      rw [Category.comp_id, Category.id_comp]
      exact ofAction_whiskerLeft L X.unop f))
    (fun {X Y} f ↦ by
      apply NatTrans.ext
      funext Z
      -- 自然変換の成分の恒等射を取り出す。
      change @eHomWhiskerRight V _ _ M _ (ofAction L) Y.unop X.unop f.unop Z ≫ 𝟙 _ =
        𝟙 _ ≫ (L.mapping.map f).app Z
      rw [Category.comp_id, Category.id_comp]
      exact ofAction_whiskerRight L f.unop Z)

/-- 写像対象への比較の順射は、各対象対で恒等射。 -/
@[reassoc]
lemma ofActionHomIso_hom_app (X Y : M) :
    ((ofActionHomIso L).hom.app (op X)).app Y = 𝟙 (L.hom X Y) :=
  rfl

/-- 写像対象への比較の逆射も、各対象対で恒等射。 -/
@[reassoc]
lemma ofActionHomIso_inv_app (X Y : M) :
    ((ofActionHomIso L).inv.app (op X)).app Y = 𝟙 (L.hom X Y) :=
  rfl

/-- B3 は作用と余テンソル随伴を保ち、写像随伴を Hom の自然同型に沿って移す。 -/
@[cite R"10.1.4"(partial:=component) "元の二つの通常随伴を保持する。"]
def ofActionTensorCotensor (L : ClosedModule V M) : @TensorCotensor V _ _ M _ (ofAction L) :=
  -- レコードの欄に同じ選択の豊穣化を渡す。
  letI := ofAction L
  { tensor := MonoidalLeftAction.curriedAction V M
    cotensor := L.cotensor
    tensorCotensor := L.cotensorAdj
    tensorHom := SerrePositivity.ParametrizedAdjunctionTransport.right
      L.mappingAdj (ofActionHomIso L).symm }

/-- B3 のテンソルは選んだ作用関手。 -/
lemma ofActionTensorCotensor_tensor :
    @TensorCotensor.tensor V _ _ M _ (ofAction L) (ofActionTensorCotensor L) = T :=
  rfl

/-- B3 の余テンソルは閉加群が指定する余テンソル。 -/
lemma ofActionTensorCotensor_cotensor :
    @TensorCotensor.cotensor V _ _ M _ (ofAction L) (ofActionTensorCotensor L) = L.cotensor :=
  rfl

/-- B3 の余テンソル随伴は、閉加群が指定する随伴。 -/
lemma ofActionTensorCotensor_tensorCotensor :
    @TensorCotensor.tensorCotensor V _ _ M _ (ofAction L) (ofActionTensorCotensor L) =
      L.cotensorAdj :=
  rfl

/-- B3 の写像随伴は、豊穣 Hom の表示で書いた閉加群の写像随伴。 -/
lemma ofActionTensorCotensor_tensorHom :
    @TensorCotensor.tensorHom V _ _ M _ (ofAction L) (ofActionTensorCotensor L) =
      SerrePositivity.ParametrizedAdjunctionTransport.right
        L.mappingAdj (ofActionHomIso L).symm :=
  rfl

/-- 選んだ普通豊穣化の上で、作用と二つの通常随伴を対応づける。
Mathlib の左作用は随伴を含まず、既存のテンソル・余テンソルは作用の整合を含まない。 -/
@[cite H"4.1.12"(partial:=component) "既存の通常豊穣化上に二つの随伴を置く補助。"]
structure ClosedModuleOn (V : Type u) (M : Type w) [Category.{v} V] [Category.{z} M]
    [MonoidalCategory V] [MonoidalLeftAction V M] [EnrichedOrdinaryCategory V M] where
  /-- 選んだ豊穣化に対する随伴のデータ。 -/
  adjunctions : TensorCotensor V M
  /-- 作用と既存のテンソルの自然同型。 -/
  tensorIso : MonoidalLeftAction.curriedAction V M ≅ adjunctions.tensor
  /-- テンソルの比較は単位と両立する。 -/
  unit_hom_app (X : M) :
    (tensorIso.hom.app (𝟙_ V)).app X ≫ adjunctions.unitIso.hom.app X =
      (MonoidalLeftAction.actionUnitNatIso V M).hom.app X

/-- テンソルの自然同型に沿って二つの随伴を移し、閉じた左加群を取り出す。 -/
@[cite H"4.1.12"(partial:=component) "二変数随伴を自然同型で輸送する補助。",
  instance_reducible]
def ClosedModuleOn.toClosedModule [EnrichedOrdinaryCategory V M]
    (S : ClosedModuleOn V M) : ClosedModule V M where
  cotensor := S.adjunctions.cotensor
  mapping := eHomFunctor V M
  cotensorAdj := SerrePositivity.ParametrizedAdjunctionTransport.left
    S.adjunctions.tensorCotensor S.tensorIso.symm
  mappingAdj := SerrePositivity.ParametrizedAdjunctionTransport.left
    S.adjunctions.tensorHom ((flipFunctor V M M).mapIso S.tensorIso.symm)

/-- 作用由来のテンソルの単位は、選んだ作用単位子に一致する。 -/
@[reassoc]
lemma ofAction_unitIso_hom_app (X : M) :
    (@TensorCotensor.unitIso V _ _ M _ (ofAction L) (ofActionTensorCotensor L)).hom.app X =
      (U X).hom := by
  -- 転置で構造の欄を読むため、戻り型と同じ豊穣化を選ぶ。
  let := ofAction L
  -- 選んだ豊穣化の Hom と作用の写像対象が同じことを明示する。
  change ((ofActionTensorCotensor L).tensorHomEquiv (𝟙_ V) X X).symm
    (actionHomEquiv L X X (𝟙 X)) = _
  rw [actionHomEquiv_id]
  refine ((ofActionTensorCotensor L).tensorHomEquiv (𝟙_ V) X X).symm_apply_eq.mpr ?_
  let e := (ofActionHomIso L).symm.app (op X)
  have h := Adjunction.homEquiv_ofNatIsoRight_apply (L.mappingAdj.adj X) e
    (X := 𝟙_ V) (Y := X) (U X).hom
  have hc := congrArg (fun k : L.hom X X ⟶ L.hom X X ↦ actionUnit L X ≫ k)
    (ofActionHomIso_inv_app L X X)
  exact (h.trans (hc.trans (Category.comp_id _))).symm

/-- 自分の作用から得た豊穣化と随伴は、同じテンソルと単位の比較を持つ。 -/
@[cite R"10.1.4"(partial:=component) "作用と通常随伴の一致を束ねる補助。"]
def ofActionClosedModuleOn (L : ClosedModule V M) : @ClosedModuleOn V M _ _ _ _ (ofAction L) :=
  -- 構造を組む際に、B3 と同じ選択の豊穣化を渡す。
  letI := ofAction L
  { adjunctions := ofActionTensorCotensor L
    tensorIso := Iso.refl _
    unit_hom_app X := by exact (Category.id_comp _).trans (ofAction_unitIso_hom_app L X) }

/-- 既存の豊穣化との比較に含める随伴は、作用の随伴を取り出した B3。 -/
lemma ofActionClosedModuleOn_adjunctions :
    @ClosedModuleOn.adjunctions V M _ _ _ _ (ofAction L) (ofActionClosedModuleOn L) =
      ofActionTensorCotensor L :=
  rfl

/-- B3 のテンソルと作用の比較は恒等自然同型。 -/
lemma ofActionClosedModuleOn_tensorIso :
    @ClosedModuleOn.tensorIso V M _ _ _ _ (ofAction L) (ofActionClosedModuleOn L) =
      Iso.refl T :=
  rfl

/-- 組紐を持つ閉モノイダル圏は自分自身の上の閉じた左加群。
Mathlib の自己作用を使い、写像側は組紐で作用の引数順を交換する。 -/
@[cite R"3.7.5"(partial:=component) "自己豊穣化に使う閉じた加群。", instance_reducible]
def closedModuleSelf (V : Type u) [Category.{v} V] [MonoidalCategory V]
    [BraidedCategory V] [MonoidalClosed V] : @ClosedModule V V _ _ _ (selfLeftAction V) where
  cotensor := MonoidalClosed.internalHom
  mapping := MonoidalClosed.internalHom
  cotensorAdj := MonoidalClosed.internalHomAdjunction₂
  mappingAdj := SerrePositivity.ParametrizedAdjunctionTransport.left
    MonoidalClosed.internalHomAdjunction₂ (curriedBraidingNatIso V)

end CategoryTheory
end
