module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectivePullbackHomClosed
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.CofibrantHomQuillen
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedMonomorphismCofibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# 標的 trivial fibration と正規化境界の pullback-Hom

概要：正規化単射と次数別全射擬同型の固定底 pullback-Hom は全射擬同型。
方針：cofibrant 両端からの Hom の右 Quillen 性、trivial fibration の引き戻し、
二対三を使い、正規化鎖の cofibrancy を代入する。
規約：一般補題は両端の cofibrancy を明示し、正規化単射への系には残さない。
使われ方：標準境界を使う固定底の実 frame の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {P Q X Y : Complex A}

/-- 概要：cofibrant 両端の相対 Hom は標的 trivial fibration に対して擬同型。
方針：Hom(P,p) の引き戻しと Hom(Q,p) から二対三を使う。
規約：i の cofibration 性や擬同型性は不要。
使われ方：正規化単射の同じ比較射への代入。 -/
lemma complexPullbackHom_quasiIso_of_target_trivial (i : P ⟶ Q) (p : X ⟶ Y)
    (hP : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P))
    (hQ : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ Q))
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) (hq : QuasiIso p) :
    QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) := by
  have h₁ := _root_.SerrePositivity.ComplexLimits.homPostcompose_cofibrant_trivialFibration P hP p hp hq
  have h₂ := _root_.SerrePositivity.ComplexLimits.homPostcompose_cofibrant_trivialFibration Q hQ p hp hq
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have : Fibration (homPostcompose P p) := ⟨h₁.1⟩
  have : WeakEquivalence (homPostcompose P p) := ⟨h₁.2⟩
  have : WeakEquivalence (pullback.snd (homPostcompose P p) (homPrecompose i Y)) :=
    inferInstance
  have : QuasiIso (pullback.snd (homPostcompose P p) (homPrecompose i Y)) :=
    (mem_quasiIso_iff _).mp (show WeakEquivalence
      (pullback.snd (homPostcompose P p) (homPrecompose i Y)) from inferInstance).mem
  have : QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.snd _ _) := by
    rw [_root_.SerrePositivity.ComplexLimits.complexPullbackHom_snd]
    exact h₂.2
  exact quasiIso_of_comp_right _ (pullback.snd (homPostcompose P p) (homPrecompose i Y))

/-- 概要：正規化単射の pullback-Hom は標的 trivial fibration に対して全射擬同型。
方針：正規化両端の cofibrancy と単射像の射影 cofibration 性を代入する。
規約：任意の小さい単体集合の単射と任意可換係数環。
使われ方：境界包含を含む固定底の相対充填。 -/
lemma normalizedPullbackHom_target_trivialFibration {K L : SSet.{0}} (f : K ⟶ L)
    [Mono f] (p : X ⟶ Y) (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) (hq : QuasiIso p) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (_root_.SerrePositivity.ComplexLimits.complexPullbackHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) p) ∧
      QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) p) :=
  ⟨_root_.SerrePositivity.ComplexLimits.complexPullbackHom_projectiveFibration _ p (_root_.SerrePositivity.ComplexLimits.normalizedMonomorphism_cofibration A f) hp,
    _root_.SerrePositivity.ComplexLimits.complexPullbackHom_quasiIso_of_target_trivial _ p
      (_root_.SerrePositivity.ComplexLimits.normalizedCochain_cofibrant A K) (_root_.SerrePositivity.ComplexLimits.normalizedCochain_cofibrant A L) hp hq⟩

/-- 概要：正規化単体境界の元の比較射は全射擬同型。
方針：正規化単射の一般補題を境界包含へ特殊化する。
規約：零単体の境界を含む全 n。
使われ方：固定底の実 pullback の境界持ち上げ。 -/
lemma normalizedBoundaryPullbackHom_target_trivialFibration (n : ℕ) (p : X ⟶ Y)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) (hq : QuasiIso p) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A
      (_root_.SerrePositivity.ComplexLimits.complexPullbackHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (SSet.boundary n).ι) p) ∧
    QuasiIso
      (_root_.SerrePositivity.ComplexLimits.complexPullbackHom ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (SSet.boundary n).ι) p) :=
  _root_.SerrePositivity.ComplexLimits.normalizedPullbackHom_target_trivialFibration (SSet.boundary n).ι p hp hq

/-- 概要：正規化単射の標準閉 pullback-Hom 自身は全射擬同型。
方針：既存の標的同型と比較射の等式で結論を移す。
規約：complexMonoidalClosed の標準比較を結論に保つ。
使われ方：標準 Arrow.pullbackHom を使う消費側への入口。 -/
lemma normalizedPullbackHomClosed_target_trivialFibration {K L : SSet.{0}} (f : K ⟶ L)
    [Mono f] (p : X ⟶ Y) (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) (hq : QuasiIso p) :
    let i := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f
    let g := ((MonoidalCategory.Arrow.pullbackHom.obj
      (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A g ∧ QuasiIso g := by
  let i := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f
  let g := ((MonoidalCategory.Arrow.pullbackHom.obj
    (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom
  have hEq : g = _root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).inv :=
    (Iso.eq_comp_inv _).mpr (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosed_compare i p)
  change _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A g ∧ QuasiIso g
  rw [hEq]
  have h := _root_.SerrePositivity.ComplexLimits.normalizedPullbackHom_target_trivialFibration f p hp hq
  have : QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) := h.2
  refine ⟨?_, inferInstance⟩
  intro n
  exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance :
    Epi ((_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).inv.f n))).comp (h.1 n)

/-- 概要：正規化単体境界の標準閉 pullback-Hom は全射擬同型。
方針：標準閉比較についての正規化単射の結論へ境界包含を代入する。
規約：任意の n と任意の次数別全射擬同型 p。
使われ方：標準比較自身を使う固定底の frame。 -/
lemma normalizedBoundaryPullbackHomClosed_target_trivialFibration (n : ℕ) (p : X ⟶ Y)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) (hq : QuasiIso p) :
    let i := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (SSet.boundary n).ι
    let g := ((MonoidalCategory.Arrow.pullbackHom.obj
      (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A g ∧ QuasiIso g :=
  _root_.SerrePositivity.ComplexLimits.normalizedPullbackHomClosed_target_trivialFibration (SSet.boundary n).ι p hp hq

end SerrePositivity.ComplexLimits
