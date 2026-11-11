module
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadout
public import SerrePositivity.KST.Fibration.ZeroMiddleControlledLongFamily

/-!
概要：指定 Verdier 両端の上側入力を、元の全 S• 再構成が使う両端へ戻す。
方針：同じ対象等号で native Hom を輸送し、元の二短辺の厳密合成へ照合する。
規約：元の零中間対象・全 S• 中間対象・両短辺を保持し、存在仮定を追加しない。
使われ方：K-6 c4 の実下側読出しを実全 S• 上側構成へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 概要：元の上側再構成が使う native 長 Hom の標的。
方針：同じ元の二端点の core Kan Hom を使う。
規約：指定両端への輸送前の座標を保持する。
使われ方：全 S• 上側構成の長 Hom 入力。 -/
abbrev verdierUpperNativeLongHomTarget (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
    (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)))

/-- 概要：元の上側 Hom と指定 Verdier 両端の Hom は同じ空間。
方針：同じ元の二端点の回収を Hom へ送る。
規約：対象同型を新たに選ばない。
使われ方：同じ長 Hom 全族の座標輸送。 -/
theorem verdierUpperNativeLongHomTarget_eq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierUpperNativeLongHomTarget d = verdierNativeLongHomTarget d :=
  congrArg₂ (fun (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) => (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))))
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))

private theorem upperNativeComposite_point_transport
    {A B C A' B' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hB : B = B') (hC : C = C')
    (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (F' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A' B') (G' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B' C')
    (hf : HEq F F') (hg : HEq G G') :
    (eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from X))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from Y)))) hA hC)).app
      (Opposite.op ⦋0⦌) (ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap F ≫ stableCoreSingleKanMap G))) =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap F' ≫ stableCoreSingleKanMap G')) := by
  cases hA
  cases hB
  cases hC
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  rfl


/-- 概要：同じ元の上側二短辺の実合成端を指定両端で回収する。
方針：core 包含と全 S• 合成を元の二つの core Kan 射へ戻し、対象等号で輸送する。
規約：元の実左辺・上辺を保持する。
使われ方：上側長 Hom 入力の全合成端条件。 -/
theorem verdierUpperReconstructionCompositePoint_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (eqToHom (verdierUpperNativeLongHomTarget_eq d)).app (Opposite.op ⦋0⦌)
      (ULift.up (SimplicialCategory.homEquiv' _ _
        (zeroMiddleControlledFirstMap (verdierUpperTriangle d) ≫
          zeroMiddleFullSKanComposite (verdierUpperTriangle d)
            (verdierUpperTriangle_middle_isZero d)))) =
      verdierNativeCompositePoint d 0 := by
  have hc : zeroMiddleControlledFirstMap (verdierUpperTriangle d) ≫
      zeroMiddleFullSKanComposite (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) =
      stableCoreSingleKanMap
          (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierUpperTriangle d))) ≫
        stableCoreSingleKanMap
          (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierUpperTriangle d))) := by
    rw [← zeroMiddleFullSKanComparison_last]
    simpa only [zeroMiddleControlledFirstMap, Category.assoc] using!
      congrArg (fun f :
        (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)).obj ⟶
          (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 1⟩)).obj =>
        f ≫ (show
          (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 1⟩)).obj ⟶
            (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)).obj from
          stableCoreSingleKanMap
            (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierUpperTriangle d)))))
        (zeroMiddleFullSKanComparison_first (verdierUpperTriangle d)
          (verdierUpperTriangle_middle_isZero d))
  have hpoint := congrArg (fun f =>
    (eqToHom (verdierUpperNativeLongHomTarget_eq d)).app (Opposite.op ⦋0⦌)
      (ULift.up (SimplicialCategory.homEquiv' _ _ f))) hc
  have hf := (stableArrowExactMap_heq (verdierUpperTriangle_first_arrow d)).trans
    (verdierLeftExactMap_original_heq d).symm
  have hg := (stableArrowExactMap_heq (verdierUpperTriangle_last_arrow d)).trans
    (verdierTopExactMap_original_heq d).symm
  exact hpoint.trans ((upperNativeComposite_point_transport
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    (verdierUpperTriangle_middle d)
    ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))
    _ _ (verdierLeftExactMap d) (verdierTopExactMap d) hf hg).trans
      (verdierNativeCompositePoint_upper d).symm)

/-- 概要：指定両端上の長 Hom 入力を元の上側再構成の座標へ戻す。
方針：同じ対象等号の逆で内部 Hom を後合成する。
規約：長 Hom の全入力を保持する。
使われ方：同じ実下側から作った上側入力を実再構成へ代入する。 -/
def verdierUpperNativeLongHomTransport (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierNativeLongHomTarget d)) :=
  q ≫ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
    (eqToHom (verdierUpperNativeLongHomTarget_eq d).symm)

/-- 概要：戻した同じ全長 Hom 入力は上側再構成の元の実合成端を回収する。
方針：評価と標的輸送を可換させ、指定合成端の回収等式で等号輸送を相殺する。
規約：全パラメータで元の二短辺の厳密合成を保持する。
使われ方：全 S• 上側族の実構成に渡す合成端条件。 -/
theorem verdierUpperNativeLongHomTransport_full (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierNativeLongHomTarget d))
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      SSet.const (verdierNativeCompositePoint d 0)) :
    verdierUpperNativeLongHomTransport d K q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      SSet.const (ULift.up (SimplicialCategory.homEquiv' _ _
        (zeroMiddleControlledFirstMap (verdierUpperTriangle d) ≫
          zeroMiddleFullSKanComposite (verdierUpperTriangle d)
            (verdierUpperTriangle_middle_isZero d)))) := by
  have he : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
      (eqToHom (verdierUpperNativeLongHomTarget_eq d).symm) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) ≫
        eqToHom (verdierUpperNativeLongHomTarget_eq d).symm := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    rfl
  rw [verdierUpperNativeLongHomTransport, Category.assoc, he, ← Category.assoc, hq,
    SSet.const_comp, ← verdierUpperReconstructionCompositePoint_target d]
  congr 1
  change ((eqToHom (verdierUpperNativeLongHomTarget_eq d) ≫
    eqToHom (verdierUpperNativeLongHomTarget_eq d).symm).app (Opposite.op ⦋0⦌)) _ = _
  rw [eqToHom_trans]
  rfl

end SerrePositivity.KST.Fibration
