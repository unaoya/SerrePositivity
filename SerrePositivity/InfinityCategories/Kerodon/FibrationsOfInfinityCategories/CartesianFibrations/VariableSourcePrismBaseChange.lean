module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VariableSourcePrismEvaluation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：動く初期値の lift データと全 lift 空間の任意のパラメーター変更。
方針：curry の自然性と引き戻しの貼り合わせ同型を用いる。
規約：底の射と全空間の prism の両方を厳密に保つ。
使われ方：始点同値を固定した fiber と既存の固定始点の lift 空間の同定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：初期値データをパラメーターで制限することは元の二つの族の制限と一致する。
方針：始点と底の二射影の curry の自然性で確認する。
規約：パラメーター射 g は任意。
使われ方：始点同値を固定する底変換。 -/
lemma prismLiftData_precomp {E B K L M : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) (g : M ⟶ L) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p ((K ◁ g) ≫ v) ((Δ[1] ◁ (K ◁ g)) ≫ δ) (by
        rw [Category.assoc, hv]
        simpa only [Category.assoc] using congrArg (fun w ↦ w ≫ δ)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 (K ◁ g)).symm) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_fst]
    exact (curry_natural_left g v).symm
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_snd]
    rw [← curry_natural_left]
    congr 1

/-- 概要：全 lift 空間の底変換は制限した初期値データの全 lift 空間と同型。
方針：引き戻しの縦の貼り合わせの標準同型を使う。
規約：パラメーター射 g は同型でなくてもよい。
使われ方：始点同値の空間の各 fiber の厳密な比較。 -/
def prismLiftSpaceBaseChangeIso {E B L M : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) (g : M ⟶ L) :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d) g ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace p K (g ≫ d) :=
  pullbackLeftPullbackSndIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π d g

/-- 概要：全 lift 空間の底変換同型は元の prism の関手空間への射を保つ。
方針：引き戻しの貼り合わせ同型の第一射影の公式。
規約：全ての高次 lift を保つ。
使われ方：底変換と終点評価の可換性。 -/
lemma prismLiftSpaceBaseChangeIso_curry {E B L M : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) (g : M ⟶ L) :
    (prismLiftSpaceBaseChangeIso p K d g).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K (g ≫ d) =
      pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- 概要：全 lift 空間の底変換同型は元のパラメーターへの射影を保つ。
方針：引き戻しの貼り合わせ同型の第二射影の公式。
規約：底変換後のパラメーターは M。
使われ方：始点同値の fiber 上の同定。 -/
lemma prismLiftSpaceBaseChangeIso_projection {E B L M : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) (g : M ⟶ L) :
    (prismLiftSpaceBaseChangeIso p K d g).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (g ≫ d) =
      pullback.snd _ _ :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

/-- 概要：全 lift 空間の底変換同型は普遍 prism の評価を保つ。
方針：関手空間への射を保つ式を展開する。
規約：底変換後の族を元の空間への射で引き戻した族と厳密に比較する。
使われ方：固定始点の終点評価の同値性を動く始点の族の fiber に移す。 -/
lemma prismLiftSpaceBaseChangeIso_prism {E B L M : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) (g : M ⟶ L) :
    (Δ[1] ◁ (K ◁ (prismLiftSpaceBaseChangeIso p K d g).hom)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism p K (g ≫ d) =
    (Δ[1] ◁ (K ◁ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d) g)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpacePrism p K d := by
  calc
    _ = (α_ Δ[1] K _).inv ≫ uncurry
        ((prismLiftSpaceBaseChangeIso p K d g).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K (g ≫ d)) := by
      rw [uncurry_natural_left]
      rfl
    _ = (α_ Δ[1] K _).inv ≫ uncurry (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d) := by
      rw [prismLiftSpaceBaseChangeIso_curry]
    _ = _ := by rw [uncurry_natural_left]; rfl

/-- 概要：データの等式による lift 空間の同型は普遍 prism の curry を保つ。
方針：等式の帰納法で恒等同型へ戻す。
規約：等式の証明の選び方には依存しない。
使われ方：固定始点との同型の評価の可換性。 -/
lemma prismLiftSpace_eqToIso_curry {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    {d e : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt} (h : d = e) :
    (eqToIso (congrArg (fun w ↦ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π w) h)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K e = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d := by
  cases h
  simp

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
