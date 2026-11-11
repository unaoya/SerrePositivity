module
public import SerrePositivity.KST.Fibration.ZeroMiddleFixedHornFamilyComparison
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryPushout
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeHomotopyInvertible

/-!
概要：同じ三面を固定する実全族比較を、上側二胞体の全境界を固定した比較へ制限する。
方針：元の固定三面 fiber 内の相対ホモトピーと F1 正本の欠面境界包含を使う。
規約：制御充填の存在は主張せず、構成済みの同じ三面の全族だけを受け取る。
使われ方：K-6 c4 の指定短辺・共有対角を全時刻で保持する上側比較。
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
  (K : SSet.{u + 1}) (F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (hF : ((horn 3 (2 : Fin 4)).ι ▷ K) ≫ F =
    fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ)

/-- 概要：元の既存充填と同じ全族の比較を、三面を固定する実ホモトピーとして保持する。
方針：同じ固定三面内の存在定理から比較を選ぶ。
規約：全族 F 自体の存在は主張しない。
使われ方：上側の短辺・共有対角の制限を同じ一つの比較から回収する。 -/
def zeroMiddleFixedHornRelativeFamilyHomotopy : SSet.Homotopy
    (fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ) F :=
  (zeroMiddleFixedHornFamily_relative_exists s hZ K F hF).choose

/-- 概要：選んだ同じ実比較は元の三面を全時刻固定する。
方針：同じ相対ホモトピーの指定回収式を使う。
規約：別の環境内比較へ取り替えない。
使われ方：元の上側全境界の同時固定を導く。 -/
theorem zeroMiddleFixedHornRelativeFamilyHomotopy_horn :
    (((horn 3 (2 : Fin 4)).ι ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (zeroMiddleFixedHornRelativeFamilyHomotopy s hZ K F hF).h =
      fst ((horn 3 (2 : Fin 4) : SSet.{u + 1}) ⊗ K) Δ[1] ≫
        fst (horn 3 (2 : Fin 4) : SSet.{u + 1}) K ≫ zeroMiddleFullSKanHorn s hZ :=
  (zeroMiddleFixedHornFamily_relative_exists s hZ K F hF).choose_spec

/-- 概要：同じ実比較を上側二胞体の全パラメータへ制限する。
方針：元の欠面 2 と全パラメータで前合成する。
規約：元の既存上側と構成済みの制御上側を保持する。
使われ方：全境界を固定する上側比較の実ホモトピー。 -/
def zeroMiddleFixedHornRelativeUpperFamilyHomotopy : SSet.Homotopy
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫
      fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ)
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F) where
  h := ((stdSimplex.δ (2 : Fin 4) ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫
    (zeroMiddleFixedHornRelativeFamilyHomotopy s hZ K F hF).h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, SSet.Homotopy.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, SSet.Homotopy.h₁]
    rfl
  rel := by ext n t; exact False.elim t.1.2

/-- 概要：同じ上側全族比較は、二短辺と共有対角を含む全境界を全時刻固定する。
方針：F1 正本の欠面境界から元のホーンへの包含で三面固定式を制限する。
規約：境界一致から上側比較を推論せず、固定三面内の実比較を先に使う。
使われ方：K-6 c4 の指定全長 Hom の再構成後に必要な境界の厳密回収。 -/
theorem zeroMiddleFixedHornRelativeUpperFamilyHomotopy_boundary :
    (((boundary 2).ι ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (zeroMiddleFixedHornRelativeUpperFamilyHomotopy s hZ K F hF).h =
      fst ((boundary 2 : SSet.{u + 1}) ⊗ K) Δ[1] ≫
        ((boundary 2).ι ▷ K) ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) ≫
          fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ := by
  change _ ≫ (((stdSimplex.δ (2 : Fin 4) ▷ K) ▷ (Δ[1] : SSet.{u + 1})) ≫ _) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.comp_whiskerRight, ← _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn_ι,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight, Category.assoc,
    zeroMiddleFixedHornRelativeFamilyHomotopy_horn]
  rw [← zeroMiddleFixedHornOriginalFamily_horn s hZ K]
  simp only [whiskerRight_fst_assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn 2 (2 : Fin 4))
    (horn 3 (2 : Fin 4)).ι, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn_ι, Category.assoc]

/-- 概要：同じ全境界固定の上側比較は、全パラメータ頂点で可逆。
方針：境界が全頂点を含むことと F1B 正本の相対ホモトピー判定を使う。
規約：同じ実ホモトピーを保ち、可逆性のために別の比較へ選び直さない。
使われ方：指定短辺・共有対角を固定したまま上側全族を関手同型にする。 -/
theorem zeroMiddleFixedHornRelativeUpperFamilyHomotopy_pointwise :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
      (zeroMiddleFixedHornRelativeUpperFamilyHomotopy s hZ K F hF) v).toTruncated := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.relativeHomotopy_pointwise_isInvertible ((boundary 2).ι ▷ K) _ _
    (zeroMiddleFixedHornRelativeUpperFamilyHomotopy s hZ K F hF)
    (zeroMiddleFixedHornRelativeUpperFamilyHomotopy_boundary s hZ K F hF)
  rintro ⟨x, k⟩
  refine ⟨(⟨x, ?_⟩, k), rfl⟩
  rw [boundary_obj_eq_univ 0 2]
  exact Set.mem_univ _

/-- 概要：全境界固定の同じ実上側比較から元の二つの全族の関手同型を得る。
方針：同じホモトピーの点ごとの可逆性を使う。
規約：制御充填の存在と指定全長 Hom の回収は別工程のまま保持する。
使われ方：K-6 c4 の制御された上側と既存上側の全パラメータ比較。 -/
def zeroMiddleFixedHornRelativeUpperFamilyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫
      fst (Δ[3] : SSet.{u + 1}) K ≫ zeroMiddleFullSKanTetrahedron s hZ)
    ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy _
    (zeroMiddleFixedHornRelativeUpperFamilyHomotopy_pointwise s hZ K F hF)

end SerrePositivity.KST.Fibration
