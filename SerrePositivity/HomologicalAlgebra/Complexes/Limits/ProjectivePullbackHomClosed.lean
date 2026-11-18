module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectivePullbackHom
public import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# 閉構造の標準 pullback-Hom との照合

概要：明示した相対 Hom と Mathlib の閉構造の pullback-Hom を同一視する。
方針：テンソル転置の自然性と閉随伴の前合成の一致で標的の実同型を作る。
規約：complexMonoidalClosed を使い、モノイダルモデル構造を仮定しない。
使われ方：標準の MonoidalCategory.Arrow.pullbackHom を使う消費側への入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {P Q X Y : Complex A} (i : P ⟶ Q) (p : X ⟶ Y)

/-- 概要：閉構造の前合成は元の Hom 前合成。
方針：テンソル転置の自然性を評価射へ適用する。
規約：元の i と標的 T を保つ。
使われ方：閉 pullback の底の射の同一視。 -/
lemma complexClosed_pre (T : Complex A) : (MonoidalClosed.pre i).app T =
    homPrecompose i T := by
  have h := tensorHomEquiv_naturality_domain i ((ihom.ev Q).app T)
  change MonoidalClosed.curry _ = MonoidalClosed.curry _ ≫ homPrecompose i T at h
  rw [← MonoidalClosed.uncurry_pre, MonoidalClosed.curry_uncurry] at h
  rw [← MonoidalClosed.uncurry_id_eq_ev, MonoidalClosed.curry_uncurry, Category.id_comp] at h
  exact h

/-- 概要：標準閉 pullback-Hom と明示的 Hom の標的の同型。
方針：底の前合成射の等式で pullback を輸送する。
規約：二つの射影を同じ順で保つ。
使われ方：標準 MonoidalCategory.Arrow.pullbackHom への結果の代入。 -/
def complexPullbackHomClosedTargetIso :
    ((MonoidalCategory.Arrow.pullbackHom.obj (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).right ≅
      _root_.SerrePositivity.ComplexLimits.complexPullbackHomTarget i p :=
  pullback.congrHom rfl (_root_.SerrePositivity.ComplexLimits.complexClosed_pre i Y)

/-- 概要：標的同型の第一射影照合。
方針：pullback.map の第一射影則。
規約：同じ Hom(P,X) への射を比較する。
使われ方：制限射の回収。 -/
@[reassoc (attr := simp)]
lemma complexPullbackHomClosedTargetIso_fst :
    (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).hom ≫ pullback.fst _ _ =
      pullback.fst ((ihom P).map p) ((MonoidalClosed.pre i).app Y) := by
  simp only [_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso, pullback.congrHom_hom]
  change pullback.lift _ _ _ ≫ _ = _
  erw [pullback.lift_fst]
  exact Category.comp_id _

/-- 概要：標的同型の第二射影照合。
方針：pullback.map の第二射影則。
規約：同じ Hom(Q,Y) への射を比較する。
使われ方：指定底の回収。 -/
@[reassoc (attr := simp)]
lemma complexPullbackHomClosedTargetIso_snd :
    (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).hom ≫ pullback.snd _ _ =
      pullback.snd ((ihom P).map p) ((MonoidalClosed.pre i).app Y) := by
  simp only [_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso, pullback.congrHom_hom]
  change pullback.lift _ _ _ ≫ _ = _
  erw [pullback.lift_snd]
  exact Category.comp_id _

/-- 概要：標準の閉 pullback-Hom は元の比較射に一致する。
方針：二つの実射影で照合する。
規約：標的の同型以外に射を置換しない。
使われ方：SM7 の標準比較自身への移送。 -/
@[reassoc (attr := simp)]
lemma complexPullbackHomClosed_compare :
    ((MonoidalCategory.Arrow.pullbackHom.obj (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom ≫
      (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).hom = _root_.SerrePositivity.ComplexLimits.complexPullbackHom i p := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso_fst, _root_.SerrePositivity.ComplexLimits.complexPullbackHom_fst]
    change pullback.lift _ _ _ ≫ _ = _
    erw [pullback.lift_fst]
    exact _root_.SerrePositivity.ComplexLimits.complexClosed_pre i X
  · rw [Category.assoc, _root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso_snd, _root_.SerrePositivity.ComplexLimits.complexPullbackHom_snd]
    change pullback.lift _ _ _ ≫ _ = _
    erw [pullback.lift_snd]
    rfl

/-- 概要：標準の閉 pullback-Hom 自身は全射擬同型。
方針：標的同型で明示的比較の全射性と擬同型性を移す。
規約：射影モデル構造を入力 instance にせず、元の二射を使う。
使われ方：固定底の実 pullback に対する SM7。 -/
lemma complexPullbackHomClosed_trivialFibration
    (hi : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i) (hq : QuasiIso i)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) :
    let f := ((MonoidalCategory.Arrow.pullbackHom.obj
      (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A f ∧ QuasiIso f := by
  let f := ((MonoidalCategory.Arrow.pullbackHom.obj
    (Opposite.op (Arrow.mk i))).obj (Arrow.mk p)).hom
  have hEq : f = _root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).inv :=
    (Iso.eq_comp_inv _).mpr (_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosed_compare i p)
  change _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A f ∧ QuasiIso f
  rw [hEq]
  have h := _root_.SerrePositivity.ComplexLimits.complexPullbackHom_trivialFibration i p hi hq hp
  have : QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) := h.2
  refine ⟨?_, inferInstance⟩
  intro n
  exact ((ModuleCat.epi_iff_surjective _).mp (inferInstance :
    Epi ((_root_.SerrePositivity.ComplexLimits.complexPullbackHomClosedTargetIso i p).inv.f n))).comp (h.1 n)

end SerrePositivity.ComplexLimits
