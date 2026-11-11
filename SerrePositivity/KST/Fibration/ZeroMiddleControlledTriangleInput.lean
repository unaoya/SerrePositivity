module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanComposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation

/-!
概要：同じ零中間二胞体の全長 Hom を、指定合成端を固定する再構成入力へ厳密に置く。
方針：元の全 S• Hom を core 包含で制限し、同じ合成端の fiber に持ち上げる。
規約：Ind-S (9) の存在は仮定せず、再構成前の実入力だけを構成する。
使われ方：K-6 c4 の制御された上側二胞体と元の core 二胞体の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

/-- 概要：元の全 S• core 包含を制御された上側の第一短辺として固定する。
方針：同じ元の包含を Ex∞ に送る。
規約：新しい比較射を選ばない。
使われ方：Ind-S (9) に渡す固定第一短辺。 -/
def zeroMiddleControlledFirstMap :
    (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩)).obj ⟶
      (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩)).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (s.obj ⟨ULift.up 0⟩))

/-- 概要：同じ固定二短辺の合成端を保持する元の長 Hom の実入力空間。
方針：同じ全 path の合成頂点での評価の実 fiber を取る。
規約：全 S• Hom の始域を元の core に制限してから入力する。
使われ方：K-6 c4 の指定全長 Hom の再構成境界への実代入。 -/
abbrev zeroMiddleControlledLongHomSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := nerve (SimplicialThickening.Path
        (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)))
      (Y := (ihom
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩)).obj).obj
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj)
      (ComposableArrows.mk₀ coherentTriangleFullPath))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩)).obj ⟶
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj from
        zeroMiddleControlledFirstMap s ≫ zeroMiddleFullSKanComposite s hZ))

/-- 概要：元の全長 Hom は同じ二短辺の指定合成端を持つ実入力点。
方針：既存の全 S• 長 Hom の合成端回収を同じ core 包含で前合成する。
規約：再構成された二胞体やその存在を入力しない。
使われ方：Ind-S (9) の指定全長 Hom 空間の元の点。 -/
def zeroMiddleControlledLongHomInput : (zeroMiddleControlledLongHomSpace s hZ) _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSKanLongHom s hZ ≫
    (pre (zeroMiddleControlledFirstMap s)).app _), ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  change ((pre (zeroMiddleControlledFirstMap s)).app _).app (Opposite.op ⦋0⦌)
    ((zeroMiddleFullSKanLongHom s hZ).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath)) = _
  rw [zeroMiddleFullSKanLongHom_composite]
  have hc := congrArg (fun F : fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) ⟶
      stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩) =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩)).obj ⟶
      (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj from
        zeroMiddleControlledFirstMap s ≫ F)) (zeroMiddleFullSKanComparison_last s hZ)
  simpa only [Category.assoc] using! hc

/-- 概要：同じ制御入力の全長 Hom は元の指定 core 二胞体の全 Hom そのもの。
方針：既存の全 S• 長 Hom の core 回収を頂点表示へ移す。
規約：合成端やホモトピー類だけの照合に弱めない。
使われ方：再構成された上側を元の指定二胞体へ照合する実データ。 -/
theorem zeroMiddleControlledLongHomInput_recovery :
    (zeroMiddleControlledLongHomInput s hZ).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (coherentTriangleLongHom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap stableCoreSingleKanEnrichedFunctor).app (Opposite.op ⦋2⦌) s)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSKanLongHom s hZ ≫
    (pre (zeroMiddleControlledFirstMap s)).app _) = _
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSKanLongHom_core s hZ)

/-- 概要：元の二短辺の合成 path は、Ind-S (9) の指定全体 path と厳密に一致する。
方針：元の二短区間の和が三頂点全体であることを照合する。
規約：path の代表を変更せず、同じ合成端の評価を比較する。
使われ方：再構成仕様の合成端 fiber へ元の制御入力を代入する際の座標回収。 -/
theorem coherentTriangleFullPath_eq_univ :
    coherentTriangleFullPath.{u} =
      (show SimplicialThickening.Path
        (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2) from
        { I := Set.univ
          left := Set.mem_univ _
          right := Set.mem_univ _
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }) := by
  apply SimplicialThickening.Path.ext
  ext k
  change (k.down ≤ 1 ∨ 1 ≤ k.down) ↔ True
  exact ⟨fun _ => True.intro, fun _ => le_total k.down 1⟩

end SerrePositivity.KST.Fibration
