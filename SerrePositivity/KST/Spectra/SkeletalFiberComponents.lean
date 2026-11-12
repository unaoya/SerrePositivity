module

public import SerrePositivity.KST.Spectra.FunctionComplexComponents
public import SerrePositivity.KST.Spectra.SphereMappingComponents
public import SerrePositivity.KST.Spectra.SkeletalFiberFunctions
public import SerrePositivity.KST.Spectra.SimplexCellSphereIso

/-!
概要：骨格の塔の fiber の連結成分を非退化セルのホモトピー群係数で表示する。
方針：厳密な fiber の関数表示、Kan 充填による積の π₀、球面の成分表示を合成する。
規約：集合の同値であり、塔の微分や群構造の比較は含まない。
使われ方：Goerss–Jardine I §7、VIII §1。骨格上の射の係数と写像空間の成分の接続。
-/

@[expose] public section

universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：セル球面の写像空間の成分を標的の正次数ホモトピー群へ移す。
方針：標準球面への同型で源を移し、境界定数単体の類を取る。
規約：球面の実際の次元は n+1。
使われ方：Goerss–Jardine I §7。セルの π₀ の係数表示。 -/
def SimplexCell.componentEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    π₀ (PointedObject.basedHom (sphere.{u} (n + 1)) Y).right ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint :=
  (π₀Functor.mapIso (PointedSimplicialSet.forget.mapIso
    ((internalHom.flip.obj Y).mapIso (sphereIso.{u} (n + 1)).symm.op))).toEquiv |>.trans
      (SphereSimplex.componentEquiv Y n)

/-- 概要：セル球面からの射の成分の係数は同じ射の境界定数単体の類。
方針：前合成の頂点表示と標準球面の代表公式を使う。
規約：商への射の向きは sphereIso の逆射。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な代表との照合。 -/
@[simp]
theorem SimplexCell.componentEquiv_familyVertex (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ) (f : sphere.{u} (n + 1) ⟶ Y) :
    componentEquiv Y n (π₀.mk (PointedMapping.familyVertex f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y (n + 1)
        ((sphereIso.{u} (n + 1)).inv ≫ f)) := by
  change SphereSimplex.componentClass Y n
    (mapπ₀ ((MonoidalClosed.pre (sphereIso.{u} (n + 1)).inv).app Y).right
      (π₀.mk (PointedMapping.familyVertex f))) = _
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, mapπ₀_mk]
  erw [PointedMapping.familyVertex_pre, SphereSimplex.componentClass_familyVertex]

/-- 概要：骨格の塔の fiber の π₀ は非退化セル上の正次数係数の関数集合。
方針：厳密な fiber の同型、関数複体の成分同値、球面の成分同値を合成する。
規約：n 段で加えるセルの次元は n+1。群の演算との比較は別工程。
使われ方：Goerss–Jardine VIII §1。骨格の係数を写像空間の連結成分で表す。 -/
def SkeletalCellAttachment.stageFiberComponentEquiv (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    π₀ (UnbasedPointedMapping.stageFiber K Y n).right ≃
      (K.nonDegenerate (n + 1) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right n Y.basepoint) :=
  (π₀Functor.mapIso (PointedSimplicialSet.forget.mapIso
    (SkeletalCellAttachment.stageFiberFunctionIso K Y n))).toEquiv |>.trans
      ((SimplicialFunctionComplex.componentEquiv _ _).trans
        (Equiv.arrowCongr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1))
          (SimplexCell.componentEquiv Y n)))

namespace SkeletalCellAttachment

/-- 概要：指定したセルの球面写像の族を実際の fiber の頂点へ移す。
方針：球面写像の頂点を関数に束ね、厳密な fiber 同型の逆射を適用する。
規約：代表の段階で構成し、Kan 条件を必要としない。
使われ方：Goerss–Jardine VIII §1。セルの係数の実際の fiber での実現。 -/
def stageFiberVertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) (n : ℕ)
    (f : K.nonDegenerate (n + 1) → (SimplexCell.sphere.{u} (n + 1) ⟶ Y)) :
    (UnbasedPointedMapping.stageFiber K Y n).right _⦋0⦌ :=
  (stageFiberFunctionIso K Y n).inv.right.app _
    (fun c ↦ PointedMapping.familyVertex (f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1) c)))

/-- 概要：fiber に実現した球面写像の族の係数は各球面写像の同じ代表の類。
方針：厳密な同型の往復を消し、各座標の球面の成分公式を適用する。
規約：球面の向きは sphereIso の逆射に固定する。
使われ方：Goerss–Jardine I §7、VIII §1。成分係数の代表レベルの検査。 -/
@[simp]
theorem stageFiberComponentEquiv_vertex (K : SSet.{u}) (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (n : ℕ)
    (f : K.nonDegenerate (n + 1) → (SimplexCell.sphere.{u} (n + 1) ⟶ Y))
    (s : K.nonDegenerate (n + 1)) :
    stageFiberComponentEquiv K Y n (π₀.mk (stageFiberVertex K Y n f)) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv Y (n + 1)
        ((SimplexCell.sphereIso.{u} (n + 1)).inv ≫ f s)) := by
  change SimplexCell.componentEquiv Y n
    (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval _ _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))
      (mapπ₀ (stageFiberFunctionIso K Y n).hom.right
        (π₀.mk ((stageFiberFunctionIso K Y n).inv.right.app _
          (fun c ↦ PointedMapping.familyVertex (f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1) c))))))) = _
  rw [← mapπ₀_mk]
  erw [← mapπ₀_comp_apply (stageFiberFunctionIso K Y n).inv.right
    (stageFiberFunctionIso K Y n).hom.right]
  have hi : (stageFiberFunctionIso K Y n).inv.right ≫
      (stageFiberFunctionIso K Y n).hom.right = 𝟙 _ :=
    (PointedSimplicialSet.forget.mapIso (stageFiberFunctionIso K Y n)).inv_hom_id
  erw [hi, mapπ₀_id_apply, mapπ₀_mk]
  change SimplexCell.componentEquiv Y n
    (π₀.mk (PointedMapping.familyVertex
      (f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cellEquiv K (n + 1)).symm s))))) = _
  rw [Equiv.apply_symm_apply, SimplexCell.componentEquiv_familyVertex]

end SkeletalCellAttachment

end

end SerrePositivity.KST.Spectra
