module

public import SerrePositivity.KST.Spectra.TriangleMappingPost
public import SerrePositivity.KST.Spectra.TriangleMappingComponents
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackSwapComparison
public import SerrePositivity.KST.Spectra.PostLoopIntegerPower

/-!
概要：loop 値の二重円の写像では、変数交換と loop の符号反転は同じ成分の作用となる。
方針：相対三角形の写像空間の自己 pullback に移し、連結射の逆元の式を使う。
規約：loop は円の Kan 置換からの点つき内部 Hom。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの随伴構造射の符号の調整。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：等しい基点へ移すと自己射の基本群への逆元としての作用は保たれる。
方針：二つの基点の等式で帰納する。
規約：各基点での自己射の基点保存の証明を明示する。
使われ方：Kerodon §3.2.5（Tag 00WD）。対角辺の制限の基点と零写像の基点の照合。 -/
theorem KanHomotopyGroup.map_inv_of_point_eq {X : SSet.{u}} [KanComplex X]
    (f : X ⟶ X) (x y : X _⦋0⦌) (h : x = y)
    (hx : f.app _ x = x) (hy : f.app _ y = y)
    (hf : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hy a = a⁻¹)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X 0 x) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f hx a = a⁻¹ := by
  subst y
  exact hf a

/-- 概要：loop 値の二重円の写像の成分では、二つの円の交換は標的の loop の符号反転と一致。
方針：三角形による自己 pullback の同型で移し、全成分を連結射で代表して逆元の式を使う。
規約：追加公理や導来写像空間の同定を使わない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。随伴構造射のホモトピー可換性の符号の証明。 -/
theorem circleSmashLoop_swap_components (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre
      (PointedObject.smashSwap PointedSimplicialSet.circle.{u} PointedSimplicialSet.circle.{u})
      (PointedObject.basedHom CirclePower.space.{u} Z)) =
    mapπ₀ (PointedObject.basedHomMap circleSmashSquare.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z)).right := by
  let L : PointedSimplicialSet.{u} := PointedObject.basedHom CirclePower.space.{u} Z
  let v : L ⟶ L := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z
  let E : PointedSimplicialSet.{u} := PointedObject.basedHom triangleDisk.{u} L
  let B : PointedSimplicialSet.{u} := PointedObject.basedHom PointedSimplicialSet.circle.{u} L
  have : KanComplex L.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex CirclePower.space Z
  have : KanComplex E.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex triangleDisk L
  have : KanComplex B.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex PointedSimplicialSet.circle L
  have : Subsingleton (π₀ E.right) := triangleDiskHom_piZero_subsingleton L
  let p : E.right ⟶ B.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre triangleDiskDiagonal.{u} L
  have : Fibration p := triangleDisk_restriction_fibration L
  let f : E.right ⟶ E.right := (PointedObject.basedHomMap triangleDisk.{u} v).right
  let g : B.right ⟶ B.right := (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} v).right
  have comm : p ≫ g = f ≫ p := PointedMapping.pre_post_comm triangleDiskDiagonal v
  let e : E.right _⦋0⦌ := PointedSimplicialSet.basepoint E
  have hf : f.app _ e = e :=
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (A := E) (B := E)
      (PointedObject.basedHomMap triangleDisk.{u} v)
  have hp : p.app _ e = PointedSimplicialSet.basepoint B :=
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (A := E) (B := B)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed triangleDiskDiagonal.{u} L)
  have hg : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B.right 0 (PointedSimplicialSet.basepoint B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (A := B) (B := B)
          (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
            (Y := L) (Z := L) v)) a = a⁻¹ := by
    intro a
    change pointedGroupMap 0 (X := B) (Y := B)
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := L) (Z := L) v) a = a⁻¹
    simpa only [zpow_neg_one] using LoopMappingClasses.groupMap_post_integer
      PointedSimplicialSet.circle.{u} Z (-1) 0 a
  have hmap : mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p f g comm) = mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap_eq_swap_on_components (E := E.right) (B := B.right) p f g comm e hf
    intro a
    exact KanHomotopyGroup.map_inv_of_point_eq g (p.app _ e)
      (PointedSimplicialSet.basepoint B) hp _ _ hg a
  let i := circleSmashMappingPairIso L
  have hinj : Function.Injective (mapπ₀ i.hom) := by
    intro a b hab
    have h := congrArg (mapπ₀ i.inv) hab
    simpa only [← mapπ₀_comp_apply, Iso.hom_inv_id, mapπ₀_id_apply] using h
  funext a
  apply hinj
  have hs := congrArg (fun k => mapπ₀ k a) (circleSmashMappingPairIso_swap L)
  have hv := congrArg (fun k => mapπ₀ k a) (circleSmashMappingPairIso_post v)
  simp only [mapπ₀_comp_apply] at hs hv
  exact hs.trans ((congrFun hmap (mapπ₀ i.hom a)).symm.trans hv.symm)

end

end SerrePositivity.KST.Spectra
