module
public import SerrePositivity.KST.Fibration.VerdierUpperLongHomTransport

/-!
概要：元の上下長 Hom の直接端を、同じ指定 Verdier 対角の全族へ戻す。
方針：対象の厳密等号による native Hom 輸送を、同じ区間評価と照合する。
規約：全パラメータを保持し、各頂点の比較だけへ弱めない。
使われ方：K-6 c4 の正規化した上下二胞体を同じ動く共有対角で貼る準備。
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

/-- 概要：指定両端の native Hom 全族から得る同じ全対角族。
方針：元の指定 coherent 区間評価を全パラメータへ適用する。
規約：指定両端を選び直さない。
使われ方：上下の元の座標から戻した共有対角の共通の比較先。 -/
def verdierNativeDiagonalFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (K : SSet.{u + 1})
    (q : K ⟶ verdierNativeLongHomTarget d) :
    (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (Δ[1] ◁ q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)))

private theorem nativeDiagonal_coordinate_transport
    {A C A' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (hA : A = A') (hC : C = C')
    (K : SSet.{u + 1})
    (q : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)))) :
    (Δ[1] ◁ q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))) =
    (Δ[1] ◁ (q ≫ eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
      (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from X))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from Y)))) hA hC))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A'))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C'))) := by
  cases hA
  cases hC
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：実下側の直接端区間族は指定 Verdier 両端への輸送後も同じ全対角族。
方針：元の下側二端点の等号を同じ native 区間評価へ適用する。
規約：全時刻・全パラメータの射の等号を保持する。
使われ方：正規化した実下側対角を共通座標へ戻す。 -/
theorem verdierLowerNativeDiagonal_transport (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (K : SSet.{u + 1}) (q : K ⟶ verdierLowerNativeLongHomTarget d) :
    (Δ[1] ◁ q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
      (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 0⟩))
      (stableCoreSingleKanObject ((verdierLowerTriangle d).obj ⟨ULift.up 2⟩))) =
      verdierNativeDiagonalFamily d K
        (q ≫ eqToHom (verdierLowerNativeLongHomTarget_eq d)) :=
  nativeDiagonal_coordinate_transport (verdierLowerTriangle_source d)
    (verdierLowerTriangle_target d) K q

/-- 概要：元の上側座標へ戻した直接端区間族は同じ指定 Verdier 全対角族。
方針：同じ上側二端点の等号による往復を区間評価で相殺する。
規約：元の coherent 区間比較と全入力を保持する。
使われ方：正規化した上下二胞体の動く共有対角を比較する。 -/
theorem verdierUpperNativeDiagonal_transport (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (K : SSet.{u + 1}) (q : K ⟶ verdierNativeLongHomTarget d) :
    (Δ[1] ◁ (q ≫ eqToHom (verdierUpperNativeLongHomTarget_eq d).symm)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison
        (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩))
        (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩))) =
      verdierNativeDiagonalFamily d K q := by
  have h := nativeDiagonal_coordinate_transport
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))
    K (q ≫ eqToHom (verdierUpperNativeLongHomTarget_eq d).symm)
  change _ = verdierNativeDiagonalFamily d K
    ((q ≫ eqToHom (verdierUpperNativeLongHomTarget_eq d).symm) ≫
      eqToHom (verdierUpperNativeLongHomTarget_eq d)) at h
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

end SerrePositivity.KST.Fibration
