module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransformationSmallness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：両端を固定した coherent な prism の族を変換空間への射に戻す。
方針：因子の交換を逆にたどり内部 Hom と区間写像空間へ二度 curry する。
規約：パラメーターの小ささや充填性は不要。
使われ方：相対射の普遍族から写像空間比較の逆向きの射を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：パラメーター付き prism を関手空間の族に戻す。
方針：因子の交換と結合子を逆にたどって curry する。
規約：三つの因子は任意。
使われ方：coherent な変換の族の実際の射への符号化。 -/
def functorParameterizedCurry {T B K X : SSet.{u}} (H : (T ⊗ B) ⊗ K ⟶ X) :
    T ⊗ K ⟶ (ihom B).obj X :=
  curry ((α_ B T K).inv ≫ ((β_ B T).hom ▷ K) ≫ H)

/-- 概要：prism を curry して戻すと元の族。
方針：curry と uncurry と構造同型の往復を消す。
規約：厳密な等式。
使われ方：復元した変換の評価の回収。 -/
lemma functorParameterizedPrism_curry {T B K X : SSet.{u}}
    (H : (T ⊗ B) ⊗ K ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (functorParameterizedCurry H) = H := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism, functorParameterizedCurry, uncurry_curry]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← comp_whiskerRight, SymmetricCategory.symmetry,
    id_whiskerRight, Category.id_comp]

/-- 概要：端点包含は結合子で区間付きの積の端点包含へ移る。
方針：次数ごとの積の三成分を計算する。
規約：両方の端点を扱う。
使われ方：復元した変換の族の固定端点。 -/
lemma prismEndpoint_associator (i : Fin 2) (B K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B ▷ K) ≫ (α_ (Δ[1] : SSet.{u}) B K).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (B ⊗ K) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：指定両端の prism の curry は対応する関手頂点に定値。
方針：uncurry の単射性と prism の端点評価を使う。
規約：i は任意の端点。
使われ方：区間写像空間の curry の入力条件。 -/
lemma functorParameterizedCurry_endpoint {B K X : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ (B ⊗ K) ⟶ X) (i : Fin 2) (F : B ⟶ X)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (B ⊗ K) ≫ H = fst B K ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ functorParameterizedCurry ((α_ Δ[1] B K).hom ≫ H) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  change uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 i K ≫ _) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex, functorParameterizedPrism_curry,
    ← Category.assoc]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i B ▷ K) ≫ (α_ Δ[1] B K).hom) ≫ H = _
  rw [prismEndpoint_associator]
  exact hi

/-- 概要：両端を指定した coherent な prism の族を変換空間への射にする。
方針：関手空間へ curry し固定端点の区間写像空間へ戻す。
規約：元の底 B とパラメーター K は任意。
使われ方：写像空間比較の逆向きの射。 -/
def coherentTransformationFamilyCurry {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints
    (functorParameterizedCurry ((α_ Δ[1] B K).hom ≫ H))
    (functorParameterizedCurry_endpoint H 0 F h₀)
    (functorParameterizedCurry_endpoint H 1 G h₁)

/-- 概要：変換空間へ戻した族の評価は元の coherent な prism の族。
方針：二つの curry の往復を続ける。
規約：因子の結合子を明示した厳密な等式。
使われ方：復元した射と元の相対射の族の比較。 -/
lemma coherentTransformationFamilyCurry_prism {B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (H : (Δ[1] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (B ⊗ K) ≫ H = fst B K ≫ F)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (B ⊗ K) ≫ H = fst B K ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (coherentTransformationFamilyCurry F G H h₀ h₁)) =
        (α_ Δ[1] B K).hom ≫ H := by
  rw [coherentTransformationFamilyCurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints,
    functorParameterizedPrism_curry]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
