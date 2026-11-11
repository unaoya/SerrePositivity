module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-!
概要：定値な底への射に沿う逆像を、頂点 fiber とパラメータの直積として表示する。
方針：pullback の射影を fiber に持ち上げ、逆は直積の両射影から作る。
規約：射影の充填性・底の quasicategory 性は要求しない。
使われ方：fiber ごとの関手の全空間の頂点 fiber を通常の関手単体集合と同定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：定値な図式の逆像は頂点 fiber とパラメータの直積。
方針：pullback の第二射影を fiber へ持ち上げ、第一射影と組にする。
規約：パラメータ T は任意。
使われ方：fiber 上の図式のパラメータ付き比較。 -/
def constantPullbackIso {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌) (T : SSet.{u}) :
    pullback (SSet.const c : T ⟶ C) p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c ⊗ T where
  hom := lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p c (pullback.snd _ p) (by
      rw [← pullback.condition, SSet.comp_const])) (pullback.fst _ p)
  inv := pullback.lift (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) T) (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, lift_snd, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, lift_fst,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p c
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, pullback.lift_snd]
    · rw [Category.assoc, lift_snd, pullback.lift_fst, Category.id_comp]

/-- 概要：定値逆像の直積表示は、fiber への射影で元の K への射影を回収する。
方針：直積の第一射影と fiber の包含を計算する。
規約：厳密な射の等式。
使われ方：パラメータの変更に対する自然性の確認。 -/
lemma constantPullbackIso_hom_fst_ι {K C : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (T : SSet.{u}) :
    (constantPullbackIso p c T).hom ≫ fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c =
      pullback.snd (SSet.const c : T ⟶ C) p := by
  dsimp only [constantPullbackIso]
  rw [← Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 概要：定値逆像の直積表示はパラメータへの射影を保つ。
方針：直積の第二射影の計算則。
規約：厳密な等式。
使われ方：族の底上の構造を固定する。 -/
lemma constantPullbackIso_hom_snd {K C : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (T : SSet.{u}) :
    (constantPullbackIso p c T).hom ≫ snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) T =
      pullback.fst (SSet.const c : T ⟶ C) p := lift_snd _ _

/-- 概要：定値逆像の直積表示はパラメータの任意の射で自然。
方針：直積の両射影を比較し、fiber 側は包含後の等式で判定する。
規約：底は同じ頂点 c に定値。
使われ方：fiber の関手圏の比較を全単体に整合する同型にする。 -/
lemma constantPullbackIso_naturality {K C T U : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (i : T ⟶ U) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk i (by simp only [Over.mk_hom, SSet.comp_const]) :
          Over.mk (SSet.const c : T ⟶ C) ⟶ Over.mk (SSet.const c : U ⟶ C)) ≫
        (constantPullbackIso p c U).hom =
      (constantPullbackIso p c T).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c ◁ i) := by
  let u : Over.mk (SSet.const c : T ⟶ C) ⟶ Over.mk (SSet.const c : U ⟶ C) :=
    Over.homMk i (by simp only [Over.mk_hom, SSet.comp_const])
  have hfst : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map u ≫
      pullback.fst (SSet.const c : U ⟶ C) p =
        pullback.fst (SSet.const c : T ⟶ C) p ≫ i :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_fst p u
  have hsnd : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map u ≫
      pullback.snd (SSet.const c : U ⟶ C) p =
        pullback.snd (SSet.const c : T ⟶ C) p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p u
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map u ≫ _ = _
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p c
    simp only [Category.assoc, constantPullbackIso_hom_fst_ι]
    rw [hsnd, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c ◁ i) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c),
      whiskerLeft_fst]
    exact (constantPullbackIso_hom_fst_ι p c T).symm
  · simp only [Category.assoc, constantPullbackIso_hom_snd]
    rw [hfst, whiskerLeft_snd, ← Category.assoc, constantPullbackIso_hom_snd]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
