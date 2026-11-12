module
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadoutEndpoints
public import SerrePositivity.KST.Fibration.VerdierOriginalNativeHomFamily

/-!
概要：実下側読出しの始端全長 Hom を、同じ指定 Verdier 両端の元の全 path 族へ戻す。
方針：元の下側二胞体と共有対角上の全 Hom の対象等号輸送を照合する。
規約：元の実読出しを保持し、長 Hom を新しく選ばない。
使われ方：K-6 c4 の元の上下全 path 比較へ同じ読出しを代入する。
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

private theorem nativeReadout_triangle_transport
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (hA : (s.obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = A)
    (hC : (s.obj ⟨ULift.up 2⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = C)
    (hAa : (a.obj ⟨ULift.up 0⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = A)
    (hCa : (a.obj ⟨ULift.up 1⟩ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) = C) :
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
      (eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
        (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from X))
          (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from Y)))) hA hC))).app
        (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌) s).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (stableTriangleHomOverDiagonal a s h ≫
          eqToHom (congrArg₂ (fun (X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) =>
            SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) X Y) hAa hCa) ≫
          stableCoreSingleKanEnrichedFunctor.map
            (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))) := by
  subst a
  cases hA
  cases hC
  simp only [eqToHom_refl]
  rfl

/-- 概要：元の実読出し始端を指定両端へ戻すと、元の指定下側全 path 族そのもの。
方針：実始端の全二胞体回収と同じ共有対角の対象輸送を順に代入する。
規約：全長 Hom の射の等号を保持する。入力は実読出しの既存回収式。
使われ方：K-6 c4 の元の上下長 Hom 比較へ渡す始端条件。 -/
theorem verdierLowerNativeReadoutCoordinates_first (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    (verdierLowerNativeLongHomTransport d Δ[1] L).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (verdierOriginalNativeHomFamily d 1)) := by
  have hp := eq_of_heq (verdierLowerNativeReadout_first d L hL)
  change ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).map
    (eqToHom (verdierLowerNativeLongHomTarget_eq d))).app (Opposite.op ⦋0⦌)
      (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  rw [hp]
  exact nativeReadout_triangle_transport (verdierLowerTriangle d) (verdierNullDiagonal d)
    (verdierTriangle_diagonal d 1) d.left d.right
    (verdierLowerTriangle_source d) (verdierLowerTriangle_target d)
    (verdierNullDiagonal_source d) (verdierNullDiagonal_target d)

private theorem nativeReadout_point_transport {P X Y : SSet.{u + 1}}
    (h : X = Y) (x : ((ihom P).obj X) _⦋0⦌) (y : ((ihom P).obj Y) _⦋0⦌)
    (hxy : HEq x y) : ((ihom P).map (eqToHom h)).app (Opposite.op ⦋0⦌) x = y := by
  cases h
  exact eq_of_heq hxy

/-- 概要：元の実読出し終端を指定両端へ戻すと、元の実包含・商の合成端の定値全 path 族。
方針：元の終端二胞体の全長 Hom の回収を同じ対象等号で輸送する。
規約：元の実読出しと実合成端を保持する。
使われ方：K-6 c4 の指定終端を持つ全長 Hom の合成への入力。 -/
theorem verdierLowerNativeReadoutCoordinates_last (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    (verdierLowerNativeLongHomTransport d Δ[1] L).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj
        (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})) (verdierNativeCompositePoint d 1)) := by
  have hk := verdierLowerKernel_nativeLongHom d
  have hv : (SSet.uliftFunctor.{u + 1, u}).map
      (SSet.const (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (SimplicialCategory.homEquiv' _ _
          (stableCoreSingleKanMap d.inclusion ≫ stableCoreSingleKanMap d.projection))) =
      SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1) := by
    rw [verdierNativeCompositePoint_lower]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hp := (verdierLowerNativeReadout_last d L hL).trans
    (heq_of_eq (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map f)) hk))
  have hp' := hp.trans (heq_of_eq (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hv))
  exact nativeReadout_point_transport (verdierLowerNativeLongHomTarget_eq d) _ _ hp'

end SerrePositivity.KST.Fibration
