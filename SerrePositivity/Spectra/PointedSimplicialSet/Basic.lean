module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Category.Pointed

/-!
# 基点付き単体的集合

## 主モデル

基点付き単体的集合を `Under (𝟙_ SSet)` として定義する。
終対象からの単体写像は零次単体の選択と同値であり、各次数の基点はその退化像となる。
忘却関手、基点の各次数での評価、基点を保つ射と面・退化写像との両立を備える。

## 比較

単体的な基点付き集合という別の記述へ送る関手を構成する。
零対象は一つの点であり、モデル構造や安定同値はまだ導入しない。
対称スペクトルの定義は、この圏の smash 積を基礎に構成する予定。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped Simplicial

/-- 基点付き単体的集合の圏。基点を選ぶ標準の under 圏を採用する。 -/
abbrev PointedSimplicialSet := PointedObject SSet.{u}

namespace PointedSimplicialSet

/-- 基点を忘れて単体的集合へ送る関手。 -/
abbrev forget : PointedSimplicialSet.{u} ⥤ SSet.{u} := PointedObject.forget

/-- 基点を零次単体として取り出す。 -/
def basepoint (X : PointedSimplicialSet.{u}) : X.right _⦋0⦌ := SSet.unitHomEquiv _ X.hom

/-- 単体的集合と零次単体から、基点付き単体的集合を作る。 -/
def ofVertex (X : SSet.{u}) (x : X _⦋0⦌) : PointedSimplicialSet.{u} :=
  Under.mk ((SSet.unitHomEquiv X).symm x)

/-- 選んだ零次単体は、構成後の基点と一致する。 -/
@[simp] lemma basepoint_ofVertex (X : SSet.{u}) (x : X _⦋0⦌) :
    basepoint (ofVertex X x) = x := (SSet.unitHomEquiv X).apply_symm_apply x

/-- 任意の次数の基点。終対象からの単体写像をその次数で評価する。 -/
def basepointAt (X : PointedSimplicialSet.{u}) (Δ : SimplexCategoryᵒᵖ) : X.right.obj Δ :=
  X.hom.app Δ PUnit.unit

/-- 面写像・退化写像は各次数の基点を保つ。
基点を与える自然変換の自然性を評価して得る。 -/
@[simp] lemma map_basepointAt (X : PointedSimplicialSet.{u})
    {Δ Γ : SimplexCategoryᵒᵖ} (f : Δ ⟶ Γ) :
    X.right.map f (basepointAt X Δ) = basepointAt X Γ := by
  exact (ConcreteCategory.congr_hom (X.hom.naturality f) PUnit.unit).symm

/-- 基点付き単体写像は、全ての次数の基点を保つ。 -/
@[simp] lemma hom_basepointAt {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (Δ : SimplexCategoryᵒᵖ) : f.right.app Δ (basepointAt X Δ) = basepointAt Y Δ := by
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app Δ) (Under.w f)) PUnit.unit

/-- 次数を固定して、基点付き集合へ評価する関手。 -/
def evaluation (Δ : SimplexCategoryᵒᵖ) : PointedSimplicialSet.{u} ⥤ Pointed.{u} where
  obj X := ⟨X.right.obj Δ, basepointAt X Δ⟩
  map f := ⟨f.right.app Δ, hom_basepointAt f Δ⟩
  map_id _ := Pointed.Hom.ext rfl
  map_comp _ _ := Pointed.Hom.ext rfl

/-- 基点付き単体的集合を、単体的な基点付き集合として記述する。
全ての次数の基点を独立に仮定せず、一つの基点の自然性から構成する。 -/
def toPointedDiagram : PointedSimplicialSet.{u} ⥤ SimplicialObject Pointed.{u} where
  obj X := {
    obj Δ := (evaluation Δ).obj X
    map f := ⟨X.right.map f, map_basepointAt X f⟩
    map_id Δ := Pointed.Hom.ext (by
      funext x
      exact ConcreteCategory.congr_hom (X.right.map_id Δ) x)
    map_comp f g := Pointed.Hom.ext (by
      funext x
      exact ConcreteCategory.congr_hom (X.right.map_comp f g) x) }
  map f := {
    app Δ := (evaluation Δ).map f
    naturality := by
      intro Δ Γ g
      apply Pointed.Hom.ext
      funext x
      exact ConcreteCategory.congr_hom (f.right.naturality g) x }
  map_id X := by ext Δ; rfl
  map_comp f g := by ext Δ; rfl

/-- 単体的な基点付き集合から、自然な基点を持つ単体的集合を作る。
各次数の基点を自然変換の成分として用い、全ての単体写像との両立を確認する。 -/
def fromPointedDiagram : SimplicialObject Pointed.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := Under.mk (show 𝟙_ SSet ⟶ X ⋙ CategoryTheory.forget Pointed from {
    app Δ := ↾fun _ ↦ (X.obj Δ).point
    naturality := by
      intro Δ Γ f
      ext x
      exact (X.map f).map_point.symm })
  map f := Under.homMk (Functor.whiskerRight f (CategoryTheory.forget Pointed)) (by
    ext Δ x
    exact (f.app Δ).map_point)
  map_id X := by ext Δ x; rfl
  map_comp f g := by ext Δ x; rfl

/-- 終対象からの基点と、単体的な基点付き集合という二つの記述は同値。
対象だけでなく射も比較し、標準の under 圏を主モデルに選ぶ根拠を与える。 -/
def pointedDiagramEquivalence : PointedSimplicialSet.{u} ≌ SimplicialObject Pointed.{u} where
  functor := toPointedDiagram
  inverse := fromPointedDiagram
  unitIso := NatIso.ofComponents (fun X ↦ Under.isoMk
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) (by
      ext Δ x
      cases x
      rfl)) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun _ ↦ Pointed.Iso.mk (Equiv.refl _) rfl) (by intros; rfl)) (by intros; rfl)


end PointedSimplicialSet
end SerrePositivity
