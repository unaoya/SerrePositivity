module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementNormalizedHom
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementColumn
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomLiftIso
/-! 概要：相対自由列の元の全要素から同じ正規化自由 Hom の全要素へ送る。
方針：元の Hom 宇宙を戻し、同じ実随伴評価の全要素写像を使う。
規約：同じ全パラメータと元の射を保持する。
使われ方：元の標準自由 Hom span による相対 pinched 族の弱同値検出。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.SimplicialModel
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の相対全要素から同じ正規化自由 Hom への実要素写像。
方針：元の down と実随伴評価の全要素写像を合成する。
規約：元の全射を保持。使われ方：同じ相対屋根の像。 -/
def freeProbeRelativeElementNormalizedIndexMap : freeProbeRelativeElementIndex A X B ⥤
    ULiftHom.{u + 1} (((((freeNormalizedProbeHom A).obj (op X)).obj B.obj).Elements)ᵒᵖ) :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ freeProbeElementNormalizedIndexMap A X B.obj

/-- 概要：元の相対全要素写像の実 nerve。
方針：同じ元の全射列を実関手で後合成する。
規約：全パラメータを保持。使われ方：元の全屋根の弱比較。 -/
def freeProbeRelativeElementNormalizedIndexNerveMap :
    nerve (freeProbeRelativeElementIndex A X B) ⟶
    nerve (ULiftHom.{u + 1}
      (((((freeNormalizedProbeHom A).obj (op X)).obj B.obj).Elements)ᵒᵖ)) where
  app _ := ↾fun Γ => Γ ⋙ freeProbeRelativeElementNormalizedIndexMap A X B
  naturality _ _ _ := rfl

/-- 概要：元の相対全要素写像は同じ down と通常全要素写像の合成。
方針：元の全単体列の関手合成を比較する。
規約：全パラメータを保持。使われ方：反転性の移送。 -/
lemma freeProbeRelativeElementNormalizedIndexMap_nerve :
    freeProbeRelativeElementNormalizedIndexNerveMap A X B =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj) ≫
        freeProbeElementNormalizedIndexNerveMap A X B.obj := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  exact (CategoryTheory.Functor.assoc Γ ULiftHom.down
    (freeProbeElementNormalizedIndexMap A X B.obj)).symm

/-- 概要：元の相対全要素写像そのものは反転される。
方針：同じ down の実同型と元の全要素写像の反転性を使う。
規約：元の実写像を検証。使われ方：同じ全相対屋根の弱同値性。 -/
lemma freeProbeRelativeElementNormalizedIndexMap_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (freeProbeRelativeElementNormalizedIndexNerveMap A X B)) := by
  have : IsIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj)) :=
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homLiftIso (freeProbeElementIndex A X B.obj)).isIso_hom
  have := freeProbeElementNormalizedIndexMap_localized_isIso A X B.obj
  rw [freeProbeRelativeElementNormalizedIndexMap_nerve, Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
