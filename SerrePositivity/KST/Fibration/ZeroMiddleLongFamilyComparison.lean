module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSComparisonReconstruction
public import SerrePositivity.KST.Fibration.CoherentTrianglePaths

/-!
概要：長 Hom 空間内の可逆比較を同じ全族と直接 path の全族へ移す。
方針：固定合成端 fiber の包含と既存の関手同型の後合成を使う。
規約：全族を保持し、頂点ごとの同型へ弱めない。厳密切断は使わない。
使われ方：K-6 c4 の正規化対角から元の指定対角への可逆移送。
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
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：指定合成端 fiber の点を同じ長 Hom 全族として読む。
方針：包含された関手頂点を標準同値で実写像へ戻す。
規約：入力の全単体を保持する。
使われ方：可逆比較の二つの実全族。 -/
def zeroMiddleLongPointFamily
    (ℓ : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌) :
    K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (stableCoreSingleKanObject (s.obj ⟨ULift.up 0⟩))
          (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm ℓ.val

/-- 概要：同じ固定合成端での可逆比較は長 Hom の全族の関手同型を与える。
方針：fiber の包含で写し、関手頂点と実全族の同値の両逆を使う。
規約：全族可逆比較を各 K 頂点の比較へ弱めない。
使われ方：採用済みの encode/read 比較を実対角へ戻す準備。 -/
def zeroMiddleLongPointFamilyIso
    (p q : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (zeroMiddleLongPointFamily s hZ K p)
      (zeroMiddleLongPointFamily s hZ K q) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleLongPointFamily s hZ K p) = p.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleLongPointFamily s hZ K q) = q.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  exact eqToIso (congrArg HomotopyCategory.mk hp) ≪≫ h ≪≫
    eqToIso (congrArg HomotopyCategory.mk hq.symm)

/-- 概要：同じ長 Hom 全族の可逆比較は直接 path 評価の全族にも移る。
方針：実全族の同型を同じ指定直接 path の評価へ後合成する。
規約：厳密な対角等式を主張せず、全時刻の関手同型を返す。
使われ方：再構成後の正規化対角を元の対角へ可逆に移送する。 -/
def zeroMiddleLongPointDirectFamilyIso
    (p q : (zeroMiddleFullSReconstructionLongSpace s hZ K) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso p q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (zeroMiddleLongPointFamily s hZ K p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath)))
      (zeroMiddleLongPointFamily s hZ K q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up (ComposableArrows.mk₀ coherentTriangleDirectPath))) :=
  (zeroMiddleLongPointFamilyIso s hZ K p q e).postcomp _

end SerrePositivity.KST.Fibration
