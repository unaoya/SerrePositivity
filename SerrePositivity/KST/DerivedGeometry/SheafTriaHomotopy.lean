module

public import SerrePositivity.KST.DerivedGeometry.LinearNativeTria
public import SerrePositivity.KST.DerivedGeometry.SheafPretriangulation

/-!
概要：層複体 dg 圏の前三角化を元の係数加群層の Mathlib ホモトピー圏と比較する。
方針：標準三角形を保つ代表加群の同値と、Hom の宇宙を戻す同値を合成する。
規約：層コホモロジーを読む元のアーベル圏を保持する。
使われ方：Drinfeld §2.4、KST D4・§10-7、Toën §3.2 の acyclic 局所化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：層複体 dg 圏の tria と元の層のホモトピー圏との圏同値。
方針：一般の複体での証明済み三角同値と宇宙調整の逆関手を合成する。
規約：acyclic の局所化はこの段階では取らない。
使われ方：Drinfeld §2.4、KST D4 の層の導来局所化。
-/
def triaHomotopyEquivalence : TriaCategory CoefficientDGBase.{u} B.Complexes ≌
    _root_.HomotopyCategory B.Modules (.up ℤ) :=
  (LinearComplex.nativeTriaEquivalence (C := B.LiftedModules) CoefficientDGBase.{u}).symm.trans
    ((show B.LiftedModules ⥤ B.Modules from ULiftHom.down).mapHomotopyCategory
      (.up ℤ)).asEquivalence

/--
概要：層の tria とホモトピー圏の比較の順関手は shift と可換。
方針：既存の二つの関手の構造を合成する。
規約：標準 shift を変更しない。
使われ方：Drinfeld §2.4、KST D4 の三角比較。
-/
instance triaHomotopyEquivalence_functorCommShift :
    B.triaHomotopyEquivalence.functor.CommShift ℤ := by
  dsimp [triaHomotopyEquivalence]
  infer_instance

/--
概要：層の tria とホモトピー圏の比較の逆関手は shift と可換。
方針：順関手の構造から随伴に整合する逆構造を得る。
規約：順逆の構造を独立に選ばない。
使われ方：Drinfeld §2.4、KST D4 の三角同値。
-/
instance triaHomotopyEquivalence_inverseCommShift :
    B.triaHomotopyEquivalence.inverse.CommShift ℤ := B.triaHomotopyEquivalence.commShiftInverse ℤ

/--
概要：層の tria とホモトピー圏の随伴全体は shift と整合的。
方針：順関手の可換性から単位・余単位の互換性を得る。
規約：同じ同値を使う。
使われ方：Drinfeld §2.4、KST D4 の局所化の移送。
-/
instance triaHomotopyEquivalence_commShift : B.triaHomotopyEquivalence.CommShift ℤ :=
  B.triaHomotopyEquivalence.commShift_of_functor ℤ

/--
概要：層の tria から元のホモトピー圏への関手は distinguished triangle を保つ。
方針：標準 cone の比較から証明した完全性と、加法的関手の複体への完全性を使う。
規約：元の Mathlib の三角構造を使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 局所化。
-/
instance triaHomotopyEquivalence_functorIsTriangulated :
    B.triaHomotopyEquivalence.functor.IsTriangulated := by
  dsimp [triaHomotopyEquivalence]
  infer_instance

/--
概要：層複体 dg 圏の tria と元の層のホモトピー圏は三角同値。
方針：同じ比較関手の distinguished triangle の保存を使う。
規約：既存の二つの三角構造を比較する。
使われ方：Drinfeld §2.4、KST D4 の Verdier 局所化。
-/
instance triaHomotopyEquivalence_isTriangulated : B.triaHomotopyEquivalence.IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (triaHomotopyEquivalence_functorIsTriangulated B)

/--
概要：tria の代表対象の像は元の層複体のホモトピー商の像と同型。
方針：代表対象の計算同型を逆同値で戻し、宇宙調整の因子分解と合成する。
規約：同じ実際の層複体を読む。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 対象の同定。
-/
def triaHomotopyRepresentableIso (K : B.Complexes) :
    B.triaHomotopyEquivalence.functor.obj (triaRepresentable CoefficientDGBase.{u} B.Complexes K) ≅
      (_root_.HomotopyCategory.quotient B.Modules (.up ℤ)).obj
        (B.complexLiftEquivalence.inverse.obj K) := by
  let E := LinearComplex.nativeTriaEquivalence (C := B.LiftedModules) CoefficientDGBase.{u}
  let Q := _root_.HomotopyCategory.quotient B.LiftedModules (.up ℤ)
  let d := (show B.LiftedModules ⥤ B.Modules from ULiftHom.down)
  let e : E.functor.obj (Q.obj K) ≅ triaRepresentable CoefficientDGBase.{u} B.Complexes K :=
    (derivedFiniteCellOver CoefficientDGBase.{u} B.Complexes Set.univ).isoMk
      (LinearComplex.nativeDerivedYoneda_objIso CoefficientDGBase.{u} K)
  exact (d.mapHomotopyCategory (.up ℤ)).mapIso
    (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app (Q.obj K)) ≪≫
      (d.mapHomotopyCategoryFactors (.up ℤ)).app K

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
