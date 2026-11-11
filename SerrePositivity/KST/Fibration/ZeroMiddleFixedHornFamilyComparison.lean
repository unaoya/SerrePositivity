module
public import SerrePositivity.KST.Fibration.ZeroMiddleFixedHornComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeDiagramHomotopy

/-!
概要：元の零中間二胞体の同じ三面を固定した実充填比較を、全パラメータ族へ拡張する。
方針：元の内ホーンのパラメータ積への F1 正本の制限定理を消費する。
規約：制御された再構成の存在は主張せず、構成済みの同じ三面の族だけを比較する。
使われ方：K-6 c4 の指定全長 Hom を回収した後、元の非指定充填を同じ fiber 内で比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
  (K : SSet.{u + 1})

/-- 概要：元の三面を全パラメータで固定する実充填空間。
方針：同じ元のホーン族への制限の実 fiber を取る。
規約：元の零中間二胞体に限る。一般の充填 API を新設しない。
使われ方：元の既存充填の定値族と制御された全族の比較場所。 -/
abbrev zeroMiddleFixedHornFamilySpace :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ))

/-- 概要：元の三面を全パラメータで固定する同じ充填空間は可縮 Kan。
方針：内ホーンの積の inner anodyne 性と F1 正本の自明 Kan 制限を使う。
規約：頂点ごとの比較へ弱めず、パラメータ族全体を保持する。
使われ方：K-6 c4 の全高次の固定三面比較。 -/
theorem zeroMiddleFixedHornFamilySpace_isContractibleKan :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (zeroMiddleFixedHornFamilySpace s hZ K) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne ((horn 3 (2 : Fin 4)).ι ▷ K)
    ((innerAnodyneExtensions.horn_ι (by decide : (0 : Fin 4) < 2)
      (by decide : (2 : Fin 4) < Fin.last 3)).whiskerRight K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 概要：元の既存充填の定値パラメータ族は同じ指定三面を厳密回収する。
方針：元のホーン回収式と積の第一射影の自然性を使う。
規約：既存の充填を再選択しない。
使われ方：元の定値族を同じ充填 fiber の指定頂点へ置く。 -/
theorem zeroMiddleFixedHornOriginalFamily_horn :
    ((horn 3 (2 : Fin 4)).ι ▷ K) ≫
      fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ =
    fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc,
    ← zeroMiddleFullSKanTetrahedron_horn]

/-- 概要：同じ三面を厳密回収する実全族は、元の指定充填 fiber の頂点。
方針：同じ全族の制限式を関手頂点の等式へ移す。
規約：全族の存在は追加仮定にしない。
使われ方：構成済みの制御族だけを固定三面比較へ渡す。 -/
def zeroMiddleFixedHornFamilyVertex
    (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
      fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ) :
    (zeroMiddleFixedHornFamilySpace s hZ K) _⦋0⦌ := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F) = _
  rw [hF]

/-- 概要：元の既存充填の定値族を同じ固定三面 fiber に保持する。
方針：元の全ホーン回収式で同じ定値族を持ち上げる。
規約：同じ実充填と同じ三面を保持する。
使われ方：制御された全パラメータ族と比較する元の指定点。 -/
def zeroMiddleFixedHornOriginalFamilyVertex :
    (zeroMiddleFixedHornFamilySpace s hZ K) _⦋0⦌ :=
  zeroMiddleFixedHornFamilyVertex s hZ K
    (fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ)
    (zeroMiddleFixedHornOriginalFamily_horn s hZ K)

variable (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hF : ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
    fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ)

/-- 概要：元の既存充填と制御全族は、同じ三面を固定する実 fiber 内で同型。
方針：同じ可縮 Kan fiber の二つの実頂点を比較する。
規約：制御全族の実構成は別工程で、その存在を主張しない。
使われ方：K-6 c4 の同じ三面を固定した比較を先に証明する条件。 -/
def zeroMiddleFixedHornFamilyComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (zeroMiddleFixedHornOriginalFamilyVertex s hZ K)
      (zeroMiddleFixedHornFamilyVertex s hZ K F hF) :=
  (zeroMiddleFixedHornFamilySpace_isContractibleKan s hZ K).vertexIso _ _

/-- 概要：同じ固定三面 fiber 内の比較は、元の全充填族間の全関手同型を与える。
方針：同じ実 fiber の包含へ元の比較を写す。
規約：境界だけの一致から直接比較せず、同じ fiber の比較を使う。
使われ方：制御された上側と既存の上側の全パラメータ比較。 -/
def zeroMiddleFixedHornFamilyFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ) F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (zeroMiddleFixedHornFamilyComparison s hZ K F hF) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)

/-- 概要：固定三面 fiber 内の比較を同じ始端上側の全族へ制限する。
方針：元の全充填比較を同じ面 2 と全パラメータで前合成する。
規約：固定三面内の比較を先に構成し、既存上側を保持する。
使われ方：指定全長 Hom を持つ制御上側と元の上側の族比較。 -/
def zeroMiddleFixedHornUpperFamilyComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫
        fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ)
      ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (zeroMiddleFixedHornFamilyFunctorIso s hZ K F hF)
    (stdSimplex.δ (2 : Fin 4) ▷ K)

/-- 概要：同じ固定三面内の比較を元の実三角柱の全パラメータ族へ戻す。
方針：元の三角柱写像と全パラメータで同じ実充填比較を前合成する。
規約：元の非指定充填の三角柱を保持し、制御全族の存在は主張しない。
使われ方：K-6 c4 の指定全四角柱への実族比較の接続。 -/
def zeroMiddleFixedHornPrismFamilyComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (fst ((Δ[2] : SSet.{u + 1}) ⊗ Δ[1]) K ≫ (zeroMiddleFullSKanPrism s hZ).h)
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ▷ K) ≫ F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (zeroMiddleFixedHornFamilyFunctorIso s hZ K F hF)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.triangleMiddlePrism ▷ K)
  rw [← Category.assoc, whiskerRight_fst, Category.assoc] at h
  exact h

include hF in
/-- 概要：元の全族比較を、同じ三面で時間によらず定値な実ホモトピーとして得る。
方針：F1B 正本の相対比較を同じ内ホーンの積へ適用する。
規約：三面全体を全パラメータ・全時刻で固定する。
使われ方：指定面の比較を実全四角柱の照合に使う際の制限回収。 -/
theorem zeroMiddleFixedHornFamily_relative_exists :
    ∃ H : SSet.Homotopy
      (fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ) F,
      (((horn 3 (2 : Fin 4)).ι ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
        fst ((horn 3 (2 : Fin 4) : SSet.{u + 1}) ⊗ K) Δ[1] ≫
          fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_homotopy_relative_innerAnodyne ((horn 3 (2 : Fin 4)).ι ▷ K)
    ((innerAnodyneExtensions.horn_ι (by decide : (0 : Fin 4) < 2)
      (by decide : (2 : Fin 4) < Fin.last 3)).whiskerRight K)
    (fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ) F
    (hF.trans (zeroMiddleFixedHornOriginalFamily_horn s hZ K).symm)
  refine ⟨H, ?_⟩
  exact hH.trans (congrArg
    (fun f => fst ((horn 3 (2 : Fin 4) : SSet.{u + 1}) ⊗ K) Δ[1] ≫ f)
    (zeroMiddleFixedHornOriginalFamily_horn s hZ K))

end SerrePositivity.KST.Fibration
