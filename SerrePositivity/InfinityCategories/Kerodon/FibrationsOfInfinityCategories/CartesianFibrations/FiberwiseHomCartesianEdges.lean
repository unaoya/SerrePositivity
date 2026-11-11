module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdgeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomCartesianCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.FiberwiseHomCocartesian

/-!
概要：cocartesian 辺を可逆に送る図式の表す相対指数の辺は cartesian。
方針：終端辺への図式の制限と curry の自然性から、外ホーンの延長条件を確認する。
規約：底の quasicategory 性は不要。
使われ方：相対指数の cartesian fibration 性の辺の判定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：cocartesian fibration の pullback の第一射影も cocartesian fibration。
方針：二つの pullback 表示の対称同型を第二射影に合成する。
規約：可変の底への射影を扱う。
使われ方：相対指数が表す図式の cocartesian 辺の指定。 -/
instance cocartesianFibration_pullback_fst {K C A : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (b : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (pullback.fst b p) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullbackSymmetry b p).hom :=
    ⟨MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations (pullbackSymmetry b p).hom⟩
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
      ((pullbackSymmetry b p).hom ≫ pullback.snd p b) := inferInstance
  rw [pullbackSymmetry_hom_comp_snd] at hc
  exact hc

/-- 概要：相対指数の辺を表すすべての図式が cocartesian 辺を可逆に送る条件。
方針：底の辺とその逆像上の図式による表現を量化する。
規約：表現の一意性により、実際には一つの表示での検証で十分。
使われ方：底や図式の等式による移送を含まない cartesian 性の判定。 -/
def FiberwiseHomInvertingEdge {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u})
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D) _⦋1⦌) : Prop :=
  ∀ (b : (Δ[1] : SSet.{u}) ⟶ C) (H : pullback b p ⟶ D),
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H) = e →
    ∀ s : (pullback b p) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b p) s →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))

/-- 概要：一つの可逆化する図式から、その辺の表現に依らない可逆化条件を得る。
方針：curry の等式から底と図式を順に一意に回収する。
規約：逆像の射影の fibration 性はこの一意性には不要。
使われ方：構成した特殊な辺の可逆化条件を他の外ホーンの表示で使う。 -/
lemma fiberwiseHomInvertingEdge_of_diagram {K C D : SSet.{u}} (p : K ⟶ C)
    (b : (Δ[1] : SSet.{u}) ⟶ C) (H : pullback b p ⟶ D)
    (hH : ∀ s : (pullback b p) _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b p) s →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    FiberwiseHomInvertingEdge p D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p b H)) := by
  intro b' H' hh
  have hf := SSet.yonedaEquiv.injective hh
  have hb : b' = b := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection p b' H', hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection]
  subst b'
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_injective p b hf
  subst H'
  exact hH

/-- 概要：相対指数の可逆化する辺は cartesian。
方針：最後の外ホーンの終端辺への図式の制限で可逆化を確認し、逆像の延長を使う。
規約：標的は quasicategory、元の射は cocartesian fibration。
使われ方：特殊な辺の存在を cartesian fibration の構造へ渡す。 -/
lemma fiberwiseHom_isCartesianEdge_of_inverting {K C D : SSet.{u}}
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] [Quasicategory D]
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D) _⦋1⦌) (he : FiberwiseHomInvertingEdge p D e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) e := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHom_isCartesianEdge_iff p e).2
  intro n b H₀ h₀
  let A := horn.{u} (n + 2) (Fin.last (n + 2))
  let j : (Δ[1] : SSet.{u}) ⟶ (A : SSet.{u}) := SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n)
  let u : Over.mk (A.ι ≫ b) ⟶ Over.mk b := Over.homMk A.ι rfl
  let v : Over.mk (j ≫ (A.ι ≫ b)) ⟶ Over.mk (A.ι ≫ b) := Over.homMk j rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanFinalHorn_extension_of_edgeRestriction n (pullback.fst b p)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map u) (pullback.fst (A.ι ≫ b) p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackProjection_isPullback p u) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map v)
    (pullback.fst (j ≫ (A.ι ≫ b)) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackProjection_isPullback p v) H₀
  apply he (j ≫ (A.ι ≫ b)) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map v ≫ H₀)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomCurry_precomp, SSet.yonedaEquiv_comp]
  simpa only [j, Equiv.apply_symm_apply] using h₀

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
