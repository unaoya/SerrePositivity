module
public import SerrePositivity.KST.Fibration.VerdierNativeCompositeFunctoriality
public import SerrePositivity.KST.Fibration.VerdierLowerNormalizedReconstruction

/-!
概要：元の下側長 Hom 全族を指定 Verdier 両端へ戻し、元の下側実合成端を回収する。
方針：元の二短辺の回収式から対象等号を取り、同じ native Hom を等号で輸送する。
規約：対象座標だけを輸送し、元の全族や比較辺を選び直さない。
使われ方：K-6 c4 の実下側読出しを指定合成端の移送構成へ渡す。
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

/-- 概要：下側二胞体の元の始域は指定した実左安定圏。
方針：元の第一短辺の始域を厳密に回収する。
規約：対象座標の等号を保持する。
使われ方：下側 native Hom の始域の座標輸送。 -/
theorem verdierLowerTriangle_source (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = d.left :=
  congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}))
    (verdierLowerTriangle_first_arrow d)

/-- 概要：下側二胞体の元の中間対象は指定した実中央安定圏。
方針：元の第一短辺の標的を厳密に回収する。
規約：元の実包含の中間対象を保持する。
使われ方：二短辺の native 合成の座標照合。 -/
theorem verdierLowerTriangle_middle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierLowerTriangle d).obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = d.middle :=
  congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}))
    (verdierLowerTriangle_first_arrow d)

/-- 概要：下側二胞体の元の標的は指定した実右安定圏。
方針：元の第二短辺の標的を厳密に回収する。
規約：対象座標の等号を保持する。
使われ方：下側 native Hom の標的の座標輸送。 -/
theorem verdierLowerTriangle_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = d.right :=
  congrArg (fun a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌ => (a.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}))
    (verdierLowerTriangle_last_arrow d)

/-- 概要：実下側の二端点の native Hom の標的空間。
方針：同じ二端点を core single Kan 座標へ送る。
規約：指定両端への輸送前の元の座標を保持する。
使われ方：実下側長 Hom 読出しの元の標的。 -/
abbrev verdierLowerNativeLongHomTarget (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
    (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩)))

/-- 概要：同じ下側 native Hom は指定 Verdier 両端の native Hom と等しい。
方針：元の二端点の対象等号を同じ core Kan Hom へ写す。
規約：新しい頂点同型を選ばず、元の対象等号だけを使う。
使われ方：下側の全長 Hom 入力を指定両端へ輸送する。 -/
theorem verdierLowerNativeLongHomTarget_eq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierLowerNativeLongHomTarget d = verdierNativeLongHomTarget d :=
  congrArg₂ (fun (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) => (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))))
    (verdierLowerTriangle_source d) (verdierLowerTriangle_target d)

private theorem lowerNativeComposite_point_transport
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

/-- 概要：実下側の合成端全族を指定両端へ戻すと元の実合成端の定値族。
方針：同じ元の二短辺の HEq と二端点の等号を、全パラメータの定値族へ適用する。
規約：元の実包含・商と元の全族を保持する。
使われ方：指定合成端の移送構成へ渡す下側の実全族境界。 -/
theorem verdierLowerReconstructionCompositeFamily_target (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (K : SSet.{u + 1}) :
    verdierLowerReconstructionCompositeFamily d K ≫
      eqToHom (verdierLowerNativeLongHomTarget_eq d) =
        SSet.const (verdierNativeCompositePoint d 1) := by
  rw [verdierLowerReconstructionCompositeFamily_eq, SSet.const_comp]
  have hf := (stableArrowExactMap_heq (verdierLowerTriangle_first_arrow d)).trans
    (heq_of_eq (stableArrowExactMap_arrow d.inclusion))
  have hg := (stableArrowExactMap_heq (verdierLowerTriangle_last_arrow d)).trans
    (heq_of_eq (stableArrowExactMap_arrow d.projection))
  have hp := lowerNativeComposite_point_transport (verdierLowerTriangle_source d)
    (verdierLowerTriangle_middle d) (verdierLowerTriangle_target d)
    (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierLowerTriangle d)))
    (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierLowerTriangle d)))
    d.inclusion d.projection hf hg
  exact congrArg (fun v => SSet.const (X := K) v)
    (hp.trans (verdierNativeCompositePoint_lower d).symm)

/-- 概要：実下側の長 Hom 全族を元の指定 Verdier 両端へ輸送する。
方針：同じ標的空間の等号で内部 Hom を後合成する。
規約：全長 Hom の全パラメータを保持する。
使われ方：元の実合成端比較を用いる上側入力の準備。 -/
def verdierLowerNativeLongHomTransport (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d)) :=
  q ≫ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
    (eqToHom (verdierLowerNativeLongHomTarget_eq d))

/-- 概要：輸送した同じ実下側長 Hom 全族は元の下側実合成端を全入力で回収する。
方針：評価と元の標的輸送の可換性を、同じ合成端全族へ適用する。
規約：入力は実読出しの合成端等式であり、存在を仮定しない。
使われ方：元の上側合成端へ移す長 Hom 構成への実代入。 -/
theorem verdierLowerNativeLongHomTransport_full (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      verdierLowerReconstructionCompositeFamily d K) :
    verdierLowerNativeLongHomTransport d K q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 1) := by
  have he : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
      (eqToHom (verdierLowerNativeLongHomTarget_eq d)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) ≫
        eqToHom (verdierLowerNativeLongHomTarget_eq d) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    rfl
  rw [verdierLowerNativeLongHomTransport, Category.assoc, he, ← Category.assoc, hq]
  exact verdierLowerReconstructionCompositeFamily_target d K

/-- 概要：同じ実下側の読出しから、指定上側合成端を持つ全長 Hom 入力を構成する。
方針：正規化の実読出しを指定両端へ輸送し、元の実合成端比較で上側へ移す。
規約：Ind-S (9) に条件付き。全入力の直接端を保つが、有限端点の上側照合は主張しない。
使われ方：K-6 c4 の共有対角を保った上側再構成へ渡す実入力。 -/
theorem verdierLowerReadout_upperInput_exists (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (h9 : zeroMiddleControlledTriangleSupply.{u}) :
    let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
    ∃ (L : (Δ[1] : SSet.{u + 1}) ⟶
        (ihom Pu).obj (verdierLowerNativeLongHomTarget d))
      (U : (Δ[1] : SSet.{u + 1}) ⟶ (ihom Pu).obj (verdierNativeLongHomTarget d)),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        verdierLowerReconstructionCompositeFamily d Δ[1] ∧
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 0) ∧
      verdierNativeLongHomStart d Δ[1] U =
        verdierNativeLongHomStart d Δ[1] (verdierLowerNativeLongHomTransport d Δ[1] L) := by
  obtain ⟨N, L, _, _, _, hL, _⟩ := verdierLowerNormalizedReconstruction_exists d h9
  let q := verdierLowerNativeLongHomTransport d Δ[1] L
  have hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u})) =
        SSet.const (verdierNativeCompositePoint d 1) :=
    verdierLowerNativeLongHomTransport_full d Δ[1] L hL
  exact ⟨L, verdierNativeLongHomShiftFamily d Δ[1] q hq, hL,
    verdierNativeLongHomShiftFamily_full d Δ[1] q hq,
    verdierNativeLongHomShiftFamily_start d Δ[1] q hq⟩

end SerrePositivity.KST.Fibration
