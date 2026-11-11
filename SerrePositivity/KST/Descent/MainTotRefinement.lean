module

public import SerrePositivity.KST.Descent.MainAugmentedTot
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
## 概要
実 Tot の指定増強比較の、段ごとの π_* 同型による不変性。
## 方針
元の指定比較の自然な正方形と L9 の実 Reedy Tot の同型保存を用いる。
## 規約
模型圏を仮定しない。細分射の各段の同型性自体はここでは証明しない。
## 使われ方
論文 補題 3.2 の Čech 比較。τ 位相の層論を指定射の実 Tot 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory SSet
open SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.Descent.Main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：増強元と各段が π_* 同型で結ばれると実 Tot 降下は同値（補題 3.2）。
方針：指定比較の自然性と実 Tot の同型保存から二方向の合成の消去を行う。
規約：全基点と零次数を含み、空な始域の問題は元の指定基点で回避する。
使われ方：細分と各段の置換を主経路の指定比較へ反映する。 -/
theorem hasTotDescent_iff_of_stagewise_piIsomorphism
    {A B : AugmentedTotDiagram.{u}} [KanComplex A.left.right] [KanComplex B.left.right]
    [∀ j, KanComplex (A.right.obj j).right] [∀ j, KanComplex (B.right.obj j).right]
    (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.left.right)
    (hstage : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.right.app j).right) :
    HasTotDescent A ↔ HasTotDescent B := by
  have hmap := PointedTotalization.replacementMap_piIsomorphism f.right hstage
  have hsquare := congrArg (fun g ↦ g.right) (totComparison_naturality f)
  change f.left.right ≫ (totComparison B).right =
    (totComparison A).right ≫ (PointedTotalization.replacementMap f.right).right at hsquare
  constructor
  · intro hA
    have hcomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.comp hA hmap
    rw [← hsquare] at hcomp
    exact KanPiIsomorphism.cancel_left_atVertex hf hcomp
      (PointedSimplicialSet.basepoint A.left)
  · intro hB
    have hcomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.comp hf hB
    rw [hsquare] at hcomp
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hmap

end SerrePositivity.KST.Descent.Main
