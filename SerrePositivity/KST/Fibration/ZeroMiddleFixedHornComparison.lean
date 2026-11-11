module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence

/-!
概要：元の零中間二胞体の同じ三面を固定した実充填空間で、既存充填を比較する。
方針：元の内ホーン制限の可縮 Kan fiber に実充填を置く。
規約：制御充填の存在は主張せず、同じ三面を固定した比較からのみ使う。
使われ方：K-6 c4 の Ind-S (9) の再構成後に必要な、元の充填との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))

/-- 概要：元の三面を固定する同じ全 tetrahedron の実充填空間。
方針：元の内ホーンへの制限の同じ fiber を使う。
規約：四面全体の可填性を任意の境界一致から推論しない。
使われ方：元の既存充填と制御充填を比較する場所。 -/
abbrev zeroMiddleFixedHornFillerSpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (horn 3 (2 : Fin 4)).ι).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (zeroMiddleFullSKanHorn s hZ))

/-- 概要：元の同じ三面を固定する実充填空間は可縮 Kan。
方針：内ホーン制限の正本の自明 Kan 性を同じ実ホーンへ適用する。
規約：元の三面の指定を保持する。
使われ方：制御充填を実際に構成した後の同じ fiber 内の比較。 -/
theorem zeroMiddleFixedHornFillerSpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroMiddleFixedHornFillerSpace s hZ) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne (horn 3 (2 : Fin 4)).ι
    (innerAnodyneExtensions.horn_ι (by decide) (by decide)) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：同じ元の三面を回収する実充填を、その指定 fiber の頂点として保持する。
方針：全内ホーンの厳密回収を関手頂点の評価へ移す。
規約：制御充填の存在を入力に追加せず、構成済みの充填だけを受け取る。
使われ方：元の充填と再構成後の充填の同じ比較への代入。 -/
def zeroMiddleFixedHornFillerVertex (F : (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : (horn 3 (2 : Fin 4)).ι ≫ F = zeroMiddleFullSKanHorn s hZ) :
    (zeroMiddleFixedHornFillerSpace s hZ) _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((horn 3 (2 : Fin 4)).ι ≫ F) = _
  rw [hF]

/-- 概要：元の既存充填は同じ三面を固定する実 fiber の指定頂点。
方針：元のホーン回収式をそのまま使う。
規約：既存の非指定充填を再選択しない。
使われ方：制御充填と比較する元の指定点。 -/
def zeroMiddleFixedHornOriginalVertex : (zeroMiddleFixedHornFillerSpace s hZ) _⦋0⦌ :=
  zeroMiddleFixedHornFillerVertex s hZ (zeroMiddleFullSKanTetrahedron s hZ)
    (zeroMiddleFullSKanTetrahedron_horn s hZ).symm

/-- 概要：実際に構成した制御充填は、元の三面を固定した同じ fiber 内で既存充填と同型。
方針：同じ可縮 Kan fiber の元の二頂点を比較する。
規約：境界の一致だけの環境比較へ弱めず、制御充填の存在は主張しない。
使われ方：K-6 c4 の制御した上側を使う前の必要な比較。 -/
def zeroMiddleFixedHornFillerComparison
    (F : (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : (horn 3 (2 : Fin 4)).ι ≫ F = zeroMiddleFullSKanHorn s hZ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (zeroMiddleFixedHornOriginalVertex s hZ)
      (zeroMiddleFixedHornFillerVertex s hZ F hF) :=
  (zeroMiddleFixedHornFillerSpace_isContractibleKan s hZ).vertexIso _ _

/-- 概要：同じ固定三面内の比較は、元の実全充填間の全関手同型も与える。
方針：実 fiber の包含で同じ比較を写す。
規約：元の比較が固定三面の fiber にあることを先に保持する。
使われ方：同じ制御 tetrahedron と既存 tetrahedron の実関手比較。 -/
def zeroMiddleFixedHornFillerFunctorIso
    (F : (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : (horn 3 (2 : Fin 4)).ι ≫ F = zeroMiddleFullSKanHorn s hZ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (zeroMiddleFullSKanTetrahedron s hZ) F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (zeroMiddleFixedHornFillerComparison s hZ F hF) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)

/-- 概要：同じ三面を固定する比較は、既存の始端上側と制御上側の全関手同型を与える。
方針：実 fiber 内から得た全 tetrahedron 比較を同じ面 2 で制限する。
規約：固定三面の比較を先に構成し、境界一致だけから上側の比較を推論しない。
使われ方：K-6 c4 の既存上側を保持した制御上側への輸送。 -/
def zeroMiddleFixedHornUpperComparison
    (F : (Δ[3] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : (horn 3 (2 : Fin 4)).ι ≫ F = zeroMiddleFullSKanHorn s hZ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (zeroMiddleFullSKanTransportedTriangle s hZ)
      (stdSimplex.δ (2 : Fin 4) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (zeroMiddleFixedHornFillerFunctorIso s hZ F hF)
    (stdSimplex.δ (2 : Fin 4))

end SerrePositivity.KST.Fibration
