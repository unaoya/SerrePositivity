module
public import SerrePositivity.KST.Fibration.VerdierMovingUpperNativeEndpoints
public import SerrePositivity.KST.Fibration.VerdierMovingUpperFactorizationCoordinates

/-!
概要：元の指定上側二胞体の全 native Hom と、同じ Verdier 両端での読出しを照合する。
方針：元の共有対角と両端の厳密等号だけで Hom 座標を輸送する。
規約：同じ元の二胞体を保持し、独立な比較関手を選ばない。
使われ方：K-6 c4 の再構成始端と実 (9b) 欠面の全 native Hom 条件。
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

private theorem upperNativeTriangle_coordinate_heq
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hA : s.obj ⟨ULift.up 0⟩ = A) (hC : s.obj ⟨ULift.up 2⟩ = C)
    (haA : a.obj ⟨ULift.up 0⟩ = A) (haC : a.obj ⟨ULift.up 1⟩ = C) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌) s).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (stableTriangleHomOverDiagonal a s h ≫
          eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
            SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y) haA haC) ≫
          stableCoreSingleKanEnrichedFunctor.map (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)
            (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)))) := by
  subst a
  cases hA
  cases hC
  simp only [eqToHom_refl]
  rfl

/-- 概要：元の上側二胞体の全 native Hom 頂点は同じ元の Verdier 両端の読出し。
方針：元の共有対角回収と同じ両端の座標等号を使う。
規約：全長 Hom 自身の HEq。使われ方：再構成始端の指定 native 条件の座標読替え。 -/
theorem verdierOriginalNativeHomFamily_upper_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
          (verdierUpperTriangle d)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 0))) := by
  have h := upperNativeTriangle_coordinate_heq (verdierUpperTriangle d) (verdierNullDiagonal d)
    (verdierTriangle_diagonal d 0) d.left d.right
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq))
    (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)
  simpa only [verdierOriginalNativeHomFamily, verdierOriginalNativeHomMap,
    verdierNullHomFamily, verdierTriangle, verdierUpperTriangle,
    verdierOriginalNativeHomTarget, Category.assoc] using h

end SerrePositivity.KST.Fibration
