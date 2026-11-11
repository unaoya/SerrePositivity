module

public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceInvariance
public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHomNaturality

/-!
# 全対象 fibrant な E 代数での終域置換の比較

概要：BM 命題 4.1・Hovey §5 の E 代数の写像空間を元の終域への frame Hom と比較する。
方針：全 E 代数の fibrancy と終域置換の自然な擬同型を使う。
規約：元の終域を保持した Hom も Kan で、比較は両変数に自然。
使われ方：一般 homotopy 極限の実際の Hom と Map^h の接続。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

/-- 概要：元の終域への cofibrant frame の Hom（Hovey §5）。
方針：始域だけを余単体的 frame に置き換える。
規約：終域とその全射を元の E 代数のまま保つ。
使われ方：極限の実際の Hom と導来写像空間を比較する。 -/
def sourceFrameHom : (operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj (𝟭 _)

/-- 概要：元の終域への frame Hom は Kan 複体（BM 命題 4.1、Hovey §5）。
方針：全 E 代数の fibrancy と frame のホーン持ち上げを使う。
規約：元の両変数への cofibrancy・fibrancy 入力は不要。
使われ方：重み付き end の Hom の Kan 性。 -/
lemma sourceFrameHom_kanComplex (X : (operad A).Algebraᵒᵖ) (Y : (operad A).Algebra) :
    SSet.KanComplex (((sourceFrameHom A).obj X).obj Y) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  have := isFibrant A Y
  exact cosimplicialHom_kanComplex _ (q.cofibrant X.unop)
    ((q.atObject X.unop).homotopicallyConstant) Y

/-- 概要：元の終域への frame Hom から選んだ Map^h への自然な比較（Hovey §5）。
方針：fibrant 置換の比較を後合成する。
規約：両変数に厳密に自然な実際の単体集合の射。
使われ方：極限の実際の Hom を導来写像空間へ移す。 -/
def sourceFrameHomComparison : sourceFrameHom A ⟶ mappingSpace A := by
  let := modelCategory A
  exact resolutionHomMapTarget
    (cosimplicialResolutionFamily (mappingCofibrantFactorization A)).obj
    (fibrantTargetComparison (mappingFibrantFactorization A))

variable {D : Type w} [Category.{v} D] (L : SSet.{u} ⥤ D)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL

/-- 概要：終域置換の比較は anodyne 反転後に同型（BM 命題 4.1、Hovey §5）。
方針：元の終域と置換後の fibrancy、比較の弱同値性に終域不変性を使う。
規約：単体集合のモデル構造は不要。
使われ方：元の終域の Hom で導来写像空間を計算する。 -/
lemma sourceFrameHomComparison_isIso (X : (operad A).Algebraᵒᵖ) (Y : (operad A).Algebra) :
    IsIso (L.map (((sourceFrameHomComparison A).app X).app Y)) := by
  let := modelCategory A
  let q := cosimplicialResolutionFamily (mappingCofibrantFactorization A)
  let r := mappingFibrantFactorization A
  have : IsFibrant ((𝟭 (operad A).Algebra).obj Y) := isFibrant A Y
  have := fibrantTarget_isFibrant r Y
  have : WeakEquivalence ((fibrantTargetComparison r).app Y) :=
    ⟨fibrantTargetComparison_weakEquivalence r Y⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_weakEquivalence_isIso (q.obj.obj X.unop) (q.cofibrant X.unop)
    L hL ((fibrantTargetComparison r).app Y)

/-- 概要：元の終域の Hom と Map^h は anodyne 反転後に二変数で自然同型（Hovey §5）。
方針：自然な比較を成分ごとの同型性から反転する。
規約：成分ごとの任意の同型の選択ではなく元の比較を使う。
使われ方：homotopy 極限の写像空間による検証。 -/
def sourceFrameHomComparisonIso :
    sourceFrameHom A ⋙ (Functor.whiskeringRight (operad A).Algebra SSet.{u} D).obj L ≅
      mappingSpace A ⋙ (Functor.whiskeringRight (operad A).Algebra SSet.{u} D).obj L := by
  let t := Functor.whiskerRight (sourceFrameHomComparison A)
    ((Functor.whiskeringRight (operad A).Algebra SSet.{u} D).obj L)
  have : ∀ X, IsIso (t.app X) := fun X => by
    have : ∀ Y, IsIso ((t.app X).app Y) :=
      fun Y => sourceFrameHomComparison_isIso A L hL X Y
    exact NatIso.isIso_of_isIso_app _
  have : IsIso t := NatIso.isIso_of_isIso_app _
  exact asIso t

end SerrePositivity.EInfinity.BarrattEccles
