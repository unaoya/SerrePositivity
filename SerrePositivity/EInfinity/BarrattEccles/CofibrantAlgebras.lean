module

public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Cofibrant E 代数の具体的な相対圏

概要：Dwyer–Kan の単体的局所化へ渡す cofibrant E 代数の相対圏を作る。
方針：具体的な転送モデルの cofibrant 対象の full subcategory を使う。
規約：任意の可換環上で、弱同値は元の複体の擬同型。
使われ方：E2b の単体的局所化の始域。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：具体的なモデルの cofibrant E 代数の full subcategory（Dwyer–Kan）。
方針：Mathlib の CofibrantObject を実際の転送モデルで評価する。
規約：モデル構造を入力仮定にせず、元の対象と全代数射を保持する。
使われ方：CAlg_R の単体的豊穣化の対象。 -/
abbrev CofibrantAlgebra : Type (u + 1) := by
  let := modelCategory A
  exact CofibrantObject (operad A).Algebra

/-- 概要：cofibrant E 代数から元の代数圏への包含（Dwyer–Kan）。
方針：同じ full subcategory の包含を使う。
規約：底の代数も射も変更しない。
使われ方：単体的局所化と元のモデル圏の比較。 -/
def cofibrantAlgebraInclusion : CofibrantAlgebra A ⥤ (operad A).Algebra := by
  let := modelCategory A
  exact CofibrantObject.ι

/-- 概要：cofibrant E 代数の弱同値は元のモデルの同じ類（Dwyer–Kan）。
方針：包含に沿って擬同型の類を引き戻す。
規約：新しい弱同値類を選ばない。
使われ方：相対圏としての単体的局所化の入力。 -/
def cofibrantAlgebraWeakEquivalences : MorphismProperty (CofibrantAlgebra A) :=
  (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
    (cofibrantAlgebraInclusion A ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A))

/-- 概要：相対圏の弱同値は恒等射と合成で閉じる（Dwyer–Kan）。
方針：元の複体の擬同型の乗法性を包含・忘却の逆像へ移す。
規約：大域モデル構造は登録しない。
使われ方：自由相対圏の余単位と単体的局所化の構成。 -/
instance cofibrantAlgebraWeakEquivalences_isMultiplicative :
    (cofibrantAlgebraWeakEquivalences A).IsMultiplicative := by
  unfold cofibrantAlgebraWeakEquivalences
  infer_instance

/-- 概要：包含先の各対象は具体的なモデルで cofibrant（Hovey §1.2）。
方針：full subcategory の対象が保持する証明を取り出す。
規約：外部からの cofibrancy 仮定は不要。
使われ方：cofibrant 対象上の Map^h の比較。 -/
lemma cofibrantAlgebra_isCofibrant (X : CofibrantAlgebra A) :
    let := modelCategory A
    IsCofibrant ((cofibrantAlgebraInclusion A).obj X) := by
  let := modelCategory A
  exact X.property

/-- 概要：包含先の各対象は fibrant（BM 命題 4.1）。
方針：元の E 代数モデルの全対象の fibrancy を使う。
規約：追加の fibrancy 仮定は不要。
使われ方：cofibrant 対象をそのまま bifibrant 対象として使う。 -/
lemma cofibrantAlgebra_isFibrant (X : CofibrantAlgebra A) :
    let := modelCategory A
    IsFibrant ((cofibrantAlgebraInclusion A).obj X) :=
  isFibrant A _

/-- 概要：相対圏の弱同値は底の擬同型そのもの（Dwyer–Kan）。
方針：包含と忘却による逆像を展開する。
規約：元の複体射を保持する。
使われ方：相対関手の弱同値保存の判定。 -/
lemma cofibrantAlgebraWeakEquivalences_iff {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraWeakEquivalences A f ↔
      QuasiIso ((cofibrantAlgebraInclusion A).map f).hom := Iff.rfl

/-- 概要：包含は元の弱同値を保つ相対関手（Dwyer–Kan）。
方針：同じ元のモデルの弱同値判定を使う。
規約：通常の局所化の比較にも同じ相対関手を使う。
使われ方：cofibrant 対象の単体的局所化から元の代数圏への比較。 -/
def cofibrantAlgebraInclusionRelative :
    let := modelCategory A
    LocalizerMorphism (cofibrantAlgebraWeakEquivalences A)
      (weakEquivalences (operad A).Algebra) := by
  let := modelCategory A
  exact ⟨cofibrantAlgebraInclusion A, fun _ _ _ h => h⟩

end SerrePositivity.EInfinity.BarrattEccles
