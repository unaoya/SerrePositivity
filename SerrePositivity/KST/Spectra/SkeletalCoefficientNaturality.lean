module

public import SerrePositivity.KST.Spectra.SkeletalFunctionNaturality
public import SerrePositivity.KST.Spectra.SkeletalFiberCoefficientGroups
public import SerrePositivity.KST.Spectra.SimplexCellPositiveNaturality

/-!
概要：骨格の fiber の群の非退化単体上の高次係数表示の自然性。
方針：fiber と関数複体の同型、座標群、球面の次数移動の自然性を合成する。
規約：係数の実際の点つき射からの誘導準同型と比較する。
使われ方：Goerss–Jardine VIII §1。幾何的微分の係数表示の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma stageFiberFunctionHomotopyEquiv_formula (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
      (UnbasedPointedMapping.stageFiber K X n).basepoint) :
    stageFiberFunctionHomotopyEquiv K X n r a =
      SimplicialFunctionComplex.pointedHomotopyEquiv
        (relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1))
        (PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X) r
        (pointedGroupMap
          (X := UnbasedPointedMapping.stageFiber K X n)
          (Y := SimplicialFunctionComplex.pointedObj
            (relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1))
            (PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X)) r
          (stageFiberFunctionIso K X n).hom a) := rfl

lemma stageFiberFunctionHomotopyEquiv_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right r
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) :
    stageFiberFunctionHomotopyEquiv K Z n r
      (pointedGroupMap (X := UnbasedPointedMapping.stageFiber K Y n)
        (Y := UnbasedPointedMapping.stageFiber K Z n) r
        (UnbasedPointedMapping.stageFiberMap K (Y := Y) (Z := Z) p n) a) =
      fun s ↦ pointedGroupMap
        (X := PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) Y)
        (Y := PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) Z) r
        (PointedObject.basedHomMap (SimplexCell.sphere.{u} (n + 1)) (Y := Y) (Z := Z) p)
        (stageFiberFunctionHomotopyEquiv K Y n r a s) := by
  let S := relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)
  let HY := PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) Y
  let HZ := PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) Z
  let hp : HY ⟶ HZ :=
    PointedObject.basedHomMap (SimplexCell.sphere.{u} (n + 1)) (Y := Y) (Z := Z) p
  have hg := congrArg (fun f : UnbasedPointedMapping.stageFiber K Y n ⟶
      SimplicialFunctionComplex.pointedObj S HZ ↦
      pointedGroupMap (X := UnbasedPointedMapping.stageFiber K Y n)
        (Y := SimplicialFunctionComplex.pointedObj S HZ) r f a)
    (stageFiberFunctionIso_natural K p n)
  simp only [pointedGroupMap_comp] at hg
  rw [stageFiberFunctionHomotopyEquiv_formula, stageFiberFunctionHomotopyEquiv_formula, hg]
  exact SimplicialFunctionComplex.pointedHomotopyEquiv_natural S hp r _

lemma stageFiberCoefficientEquiv_formula (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
      (UnbasedPointedMapping.stageFiber K X n).basepoint) (s : K.nonDegenerate (n + 1)) :
    stageFiberCoefficientEquiv K X n r a s = SimplexCell.positiveHomotopyEquiv X n r
      (stageFiberFunctionHomotopyEquiv K X n r a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s)) := rfl

/-- 概要：fiber の群の高次係数表示は係数射に自然。
方針：各非退化単体で関数複体の群とセルの球面の次数移動の自然性を合成する。
規約：係数の誘導準同型の次数は n+r+2。
使われ方：Goerss–Jardine VIII §1。係数微分の可換式の入力。 -/
theorem stageFiberCoefficientEquiv_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y n).right r
      (UnbasedPointedMapping.stageFiber K Y n).basepoint) :
    stageFiberCoefficientEquiv K Z n r
      (pointedGroupMap (X := UnbasedPointedMapping.stageFiber K Y n)
        (Y := UnbasedPointedMapping.stageFiber K Z n) r
        (UnbasedPointedMapping.stageFiberMap K (Y := Y) (Z := Z) p n) a) =
      fun s ↦ pointedGroupMap (n + 1 + r) p (stageFiberCoefficientEquiv K Y n r a s) := by
  funext s
  rw [stageFiberCoefficientEquiv_formula, stageFiberCoefficientEquiv_formula,
    stageFiberFunctionHomotopyEquiv_natural]
  exact SimplexCell.positiveHomotopyEquiv_natural p n r _

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
