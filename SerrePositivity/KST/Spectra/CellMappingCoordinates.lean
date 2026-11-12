module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientNaturality
public import SerrePositivity.KST.Spectra.SkeletalFiberComponents

/-!
概要：fiber の正次数係数と連結成分係数に共通する球面制限の射。
方針：余積 Hom の評価を厳密な前合成として記述し、各次数の群へ送る。
規約：セル球面の向きを固定する厳密な射を使う。
使われ方：Goerss–Jardine I §7、VIII §1。連結準同型の係数比較の入力。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セル球面を全セルの cofiber へ含める。
方針：球面の余積への包含を標準同型の逆射で戻す。
規約：商射と可換な向きに固定した包含。
使われ方：Goerss–Jardine VIII §1。全次数の係数に共通する源の射。 -/
def cellSphereInclusion (K : SSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    SimplexCell.sphere.{u} d ⟶ cellCofiber K d :=
  Limits.Sigma.ι (fun _ : relativeCellComplexOfMono.Cell (K.skeleton d).ι d ↦
    SimplexCell.sphere.{u} d) c ≫ (cellCoproductIso K d).inv

@[reassoc]
lemma cellHomFunctionIso_pointedEval (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (d : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton d).ι d) :
    (cellHomFunctionIso K Y d).hom ≫ SimplicialFunctionComplex.pointedEval _ _ c =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (cellSphereInclusion K d c) Y := by
  apply Under.UnderMorphism.ext
  change ((MonoidalClosed.pre (cellCoproductIso K d).inv).app Y).right ≫
    ((pointedCoproductHomUnderlyingIso _ _ Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval _ _ c) = _
  rw [pointedCoproductHomUnderlyingIso_eval]
  change (((MonoidalClosed.pre (cellCoproductIso K d).inv).app Y) ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _ Y).right = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  rfl

@[reassoc]
lemma stageFiberFunctionIso_pointedEval (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (c : relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)) :
    (stageFiberFunctionIso K Y n).hom ≫ SimplicialFunctionComplex.pointedEval _ _ c =
      (stageFiberCellIso K Y n).inv ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (cellSphereInclusion K (n + 1) c) Y := by
  change ((stageFiberCellIso K Y n).inv ≫ (cellHomFunctionIso K Y (n + 1)).hom) ≫ _ = _
  rw [Category.assoc, cellHomFunctionIso_pointedEval]

/-- 概要：fiber の正次数の係数を実際のセル球面への制限の群写像で計算する。
方針：関数複体の群の座標表示と評価の射の式を合成する。
規約：連結成分の係数で用いた球面と同じ向きを保つ。
使われ方：Goerss–Jardine VIII §1。塔の微分の各セルでの計算への帰着。 -/
lemma stageFiberCoefficientEquiv_restriction (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right r
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K Y n r a s = SimplexCell.positiveHomotopyEquiv Y n r
      (pointedGroupMap r (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) Y)
        (pointedGroupMap r (stageFiberCellIso K Y n).inv a)) := by
  rw [stageFiberCoefficientEquiv_formula, stageFiberFunctionHomotopyEquiv_formula,
    SimplicialFunctionComplex.pointedHomotopyEquiv_eval, ← pointedGroupMap_comp,
    stageFiberFunctionIso_pointedEval, pointedGroupMap_comp]

/-- 概要：fiber の連結成分係数も正次数と同じセル球面への制限で計算する。
方針：関数複体の成分表示と評価の射の式を合成する。
規約：正次数の係数公式と同じ包含射を使用する。
使われ方：Goerss–Jardine VIII §1。成分による代表計算と正次数群の比較。 -/
lemma stageFiberComponentEquiv_restriction (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) (a : π₀ (UnbasedPointedMapping.stageFiber K Y n).right)
    (s : K.nonDegenerate (n + 1)) :
    stageFiberComponentEquiv K Y n a s = SimplexCell.componentEquiv Y n
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) Y).right
        (mapπ₀ (stageFiberCellIso K Y n).inv.right a)) := by
  have he := congrArg Under.Hom.right (stageFiberFunctionIso_pointedEval K Y n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))
  change (stageFiberFunctionIso K Y n).hom.right ≫
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s) =
      (stageFiberCellIso K Y n).inv.right ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
        (cellSphereInclusion K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) Y).right at he
  change SimplexCell.componentEquiv Y n
    (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))
      (mapπ₀ (stageFiberFunctionIso K Y n).hom.right a)) = _
  erw [← mapπ₀_comp_apply, he, mapπ₀_comp_apply]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
