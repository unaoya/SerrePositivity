module

public import SerrePositivity.KST.Spectra.SimplexCellCofiber
public import SerrePositivity.KST.Spectra.PointedCoproductHom

/-!
概要：骨格の塔の fiber を各球面からの Hom の関数複体で表示する。
方針：セルの cofiber の余積を内部 Hom へ送り、関数複体の群の同型を適用する。
規約：係数の次数移動と境界準同型の計算はまだ含まない。
使われ方：Goerss–Jardine I §7、VIII §1。塔の各セルの寄与への分解。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セルの cofiber からの Hom は各球面の Hom の関数複体。
方針：cofiber の余積表示を反変 Hom で送り、余積の Hom の自然同型を合成する。
規約：添字は付け加える非退化セル。
使われ方：Goerss–Jardine VIII §1。各セルの寄与の厳密な点つき表示。 -/
def cellHomFunctionIso (K : SSet.{u}) (X : PointedSimplicialSet.{u}) (d : ℕ) :
    PointedObject.basedHom (cellCofiber K d) X ≅
      SimplicialFunctionComplex.pointedObj
        (relativeCellComplexOfMono.Cell (K.skeleton d).ι d)
        (PointedObject.basedHom (SimplexCell.sphere.{u} d) X) :=
  (internalHom.flip.obj X).mapIso (cellCoproductIso K d).symm.op ≪≫
    pointedCoproductHomIso _ _ X

/-- 概要：骨格の塔の fiber は球面からの Hom のセルごとの関数複体。
方針：fiber の cofiber 表示とセルの Hom の関数表示を合成する。
規約：段 n の追加セルの次元は n+1。
使われ方：Goerss–Jardine VIII §1。tower の正次数群の関数表示への比較。 -/
def stageFiberFunctionIso (K : SSet.{u}) (X : PointedSimplicialSet.{u}) (n : ℕ) :
    UnbasedPointedMapping.stageFiber K X n ≅
      SimplicialFunctionComplex.pointedObj
        (relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1))
        (PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X) :=
  (stageFiberCellIso K X n).symm ≪≫ cellHomFunctionIso K X (n + 1)

/-- 概要：塔の fiber の正次数群を各球面の Hom の正次数群の関数で表示する。
方針：実際の点つき同型を群へ送り、関数複体の座標ごとの群の同型を合成する。
規約：r は実際の次数 r+1。球面による次数移動をまだ主張しない。
使われ方：Goerss–Jardine I §7、VIII §1。境界写像をセルごとの座標で計算する入力。 -/
def stageFiberFunctionHomotopyEquiv (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K X n).right r
        (UnbasedPointedMapping.stageFiber K X n).basepoint ≃*
      (relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X).right r
          (PointedSimplicialSet.basepoint
            (PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X))) := by
  let S := relativeCellComplexOfMono.Cell (K.skeleton (n + 1)).ι (n + 1)
  let H : PointedSimplicialSet.{u} :=
    PointedObject.basedHom (SimplexCell.sphere.{u} (n + 1)) X
  let e : (UnbasedPointedMapping.stageFiber K X n).right ≅
      (SimplicialFunctionComplex.pointedObj S H).right :=
    PointedSimplicialSet.forget.mapIso (stageFiberFunctionIso K X n)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r e
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberFunctionIso K X n).hom)).trans
      (SimplicialFunctionComplex.pointedHomotopyEquiv S H r)

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
