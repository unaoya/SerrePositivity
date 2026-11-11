module
public import SerrePositivity.KST.Fibration.VerdierLowerNativeReadout
public import SerrePositivity.KST.Fibration.VerdierFullSLowerKernelTriangle

/-!
概要：元の下側全変形の読出し両端を、指定した元の二胞体へ厳密に戻す。
方針：同じ実ホモトピーの端点回収と、最大化の元の実合成二単体との照合を使う。
規約：元の全二胞体を保持し、共有対角を定値と主張しない。
使われ方：K-6 c4 の指定長 Hom を保つ有限端点の照合。
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

/-- 概要：実下側全変形の始端は元の下側全二胞体の同じ core S• 像。
方針：同じホモトピーの始端を回収し、元の対象読み替えを適用する。
規約：二短辺だけでなく元の全二単体の等号を保持する。
使われ方：実読出し始端の全 native Hom の照合。 -/
theorem verdierLowerDeformation_native_first (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
        (verdierLowerTriangle d) := by
  change SSet.yonedaEquiv (SSet.ι₀ ≫ (verdierFullSLowerDeformation d).h) = _
  rw [(verdierFullSLowerDeformation d).h₀, Equiv.apply_symm_apply,
    stableCoreSingleKanInfinity_eq]
  rfl

/-- 概要：実下側全変形の終端は指定実包含・商の同じ標準合成二胞体。
方針：同じホモトピーの終端と、最大化の既存の厳密回収を使う。
規約：元の実包含・実商と全二単体を保持する。
使われ方：実読出し終端の全 native Hom の照合。 -/
theorem verdierLowerDeformation_native_last (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (stableCoreSingleKanMap d.inclusion)
        (stableCoreSingleKanMap d.projection)).simplex := by
  change SSet.yonedaEquiv (SSet.ι₁ ≫ (verdierFullSLowerDeformation d).h) = _
  rw [(verdierFullSLowerDeformation d).h₁, Equiv.apply_symm_apply]
  exact verdierFullSLowerMaximalization_eq_kernelCompStruct d

private theorem nativeReadoutPoint_congr (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌) (h : s = t) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  subst t
  rfl

/-- 概要：同じ下側読出しの始端は元の下側全 native Hom を保持する。
方針：入力点の読出し HEq を、実始端の全二胞体回収へ代入する。
規約：入力は読出し回収式であり、新たな存在仮定を取らない。
使われ方：同じ元の全長 Hom と実合成端比較の始端照合。 -/
theorem verdierLowerNativeReadout_first (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌)
          (verdierLowerTriangle d)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) :=
  hL.trans (nativeReadoutPoint_congr _ _ (verdierLowerDeformation_native_first d))

/-- 概要：同じ下側読出しの終端は元の実包含・商の標準合成二胞体の全 native Hom。
方針：入力点の読出し HEq を、実終端の全二胞体回収へ代入する。
規約：合成端の一点だけの比較へ弱めない。
使われ方：有限終端で指定する元の全長 Hom の照合。 -/
theorem verdierLowerNativeReadout_last (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})
    (L : (Δ[1] : SSet.{u + 1}) ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj (verdierLowerNativeLongHomTarget d))
    (hL : HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (verdierFullSLowerDeformation d).h
          (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) :
    HEq (L.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (stableCoreSingleKanMap d.inclusion)
          (stableCoreSingleKanMap d.projection)).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) :=
  hL.trans (nativeReadoutPoint_congr _ _ (verdierLowerDeformation_native_last d))

/-- 概要：実包含・商の標準合成二胞体の全長 Hom は同じ実合成端の定値族。
方針：元の厳密二射列の native Hom 作用を全 path・全次数で計算する。
規約：辺のホモトピー類や一つの path の評価だけに弱めない。
使われ方：下側読出し終端を指定された定値長 Hom へ戻す。 -/
theorem verdierLowerKernel_nativeLongHom (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (stableCoreSingleKanMap d.inclusion)
      (stableCoreSingleKanMap d.projection)).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      SSet.const (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u})
        (SimplicialCategory.homEquiv' _ _
          (stableCoreSingleKanMap d.inclusion ≫ stableCoreSingleKanMap d.projection)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

end SerrePositivity.KST.Fibration
