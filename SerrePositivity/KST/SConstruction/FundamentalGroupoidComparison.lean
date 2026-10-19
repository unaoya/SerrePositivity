module
public import SerrePositivity.KST.SConstruction.FundamentalNerveHomotopy
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-! # 元の辺と二単体の基本亜群から Kan 対象への比較
概要：任意の単体集合のホモトピー圏を亜群化し、Kan 値写像で誘導される比較を作る。
方針：自由亜群の普遍性と、nerve 値写像の anodyne 延長を組み合わせる。
規約：辺の形式的逆と二単体の関係を保つ。使われ方：K 空間の生成・関係の表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories

/-- 元の頂点・辺と二単体の合成関係から作る基本亜群。 -/
abbrev simplicialFundamentalGroupoid (A : SSet.{u}) := FreeGroupoid (hoFunctor.obj A)

/-- 元の単体集合からその辺と二単体の基本亜群の nerve への標準射。 -/
def fundamentalGroupoidNerveUnit (A : SSet.{u}) :
    A ⟶ nerve (simplicialFundamentalGroupoid A) :=
  fundamentalNerveTranspose (FreeGroupoid.of (hoFunctor.obj A))

/-- Kan 値写像から、元の辺と二単体の基本亜群上の比較関手を作る。 -/
def fundamentalGroupoidComparison {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B) :
    simplicialFundamentalGroupoid A ⥤ hoFunctor.obj B := by
  letI : Groupoid (hoFunctor.obj B) := Groupoid.ofIsGroupoid
  exact FreeGroupoid.lift (hoFunctor.map i).toFunctor

/-- 比較関手は元のホモトピー圏の射を厳密に回収する。 -/
lemma fundamentalGroupoidComparison_fac {A B : SSet.{u}} [KanComplex B] (i : A ⟶ B) :
    FreeGroupoid.of (hoFunctor.obj A) ⋙ fundamentalGroupoidComparison i =
      (hoFunctor.map i).toFunctor := by
  let : Groupoid (hoFunctor.obj B) := Groupoid.ofIsGroupoid
  exact FreeGroupoid.lift_spec (hoFunctor.map i).toFunctor

/-- 基本亜群の nerve への標準射は、任意の anodyne 射に沿って延長できる。 -/
lemma exists_fundamentalGroupoidExtension {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) :
    ∃ f : B ⟶ nerve (simplicialFundamentalGroupoid A),
      i ≫ f = fundamentalGroupoidNerveUnit A := by
  have : HasLiftingProperty i (terminal.from (nerve (simplicialFundamentalGroupoid A))) :=
    hi _ (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let sq : CommSq (fundamentalGroupoidNerveUnit A) i
      (terminal.from (nerve (simplicialFundamentalGroupoid A))) (terminal.from B) :=
    ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 元の基本亜群の nerve 値写像の anodyne 延長を一つ選ぶ。 -/
def fundamentalGroupoidExtension {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) : B ⟶ nerve (simplicialFundamentalGroupoid A) :=
  Classical.choose (exists_fundamentalGroupoidExtension i hi)

/-- 選んだ延長は元の基本亜群への標準射を厳密に回収する。 -/
lemma fundamentalGroupoidExtension_fac {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) :
    i ≫ fundamentalGroupoidExtension i hi = fundamentalGroupoidNerveUnit A :=
  Classical.choose_spec (exists_fundamentalGroupoidExtension i hi)

/-- anodyne 延長の転置を戻して、元の基本亜群への逆向き関手を作る。 -/
def fundamentalGroupoidInverse {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) : hoFunctor.obj B ⥤ simplicialFundamentalGroupoid A :=
  fundamentalNerveUntranspose (fundamentalGroupoidExtension i hi)

/-- 逆向き関手は元のホモトピー圏上で標準の亜群化を厳密に回収する。 -/
lemma fundamentalGroupoidInverse_pre {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) :
    (hoFunctor.map i).toFunctor ⋙ fundamentalGroupoidInverse i hi =
      FreeGroupoid.of (hoFunctor.obj A) := by
  exact (fundamentalNerveUntranspose_pre i (fundamentalGroupoidExtension i hi)).symm.trans
    ((congrArg fundamentalNerveUntranspose (fundamentalGroupoidExtension_fac i hi)).trans
      (fundamentalNerveUntranspose_transpose (FreeGroupoid.of (hoFunctor.obj A))))

/-- Kan 値 anodyne 比較と逆向き関手の合成は、元の基本亜群上で恒等関手。 -/
lemma fundamentalGroupoidComparison_leftInverse {A B : SSet.{u}} [KanComplex B]
    (i : A ⟶ B) (hi : anodyneExtensions i) :
    fundamentalGroupoidComparison i ⋙ fundamentalGroupoidInverse i hi =
      𝟭 (simplicialFundamentalGroupoid A) := by
  apply FreeGroupoid.lift_unique'
  rw [← CategoryTheory.Functor.assoc, fundamentalGroupoidComparison_fac,
    fundamentalGroupoidInverse_pre, CategoryTheory.Functor.comp_id]

end SerrePositivity.KST.SConstruction
