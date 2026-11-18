module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ProjectiveComponentLifting
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveHomotopyInverse
public import SerrePositivity.HomologicalAlgebra.Complexes.HomRestriction
public import SerrePositivity.HomologicalAlgebra.Complexes.HomHomotopy
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# 射影 trivial cofibration の固定底 pullback-Hom

概要：次数別全射に対する実 pullback-Hom は次数別全射かつ擬同型。
方針：codisk による成分の持ち上げで全射性を示す。前合成の鎖ホモトピー同値と
trivial fibration の引き戻し安定性から、同じ比較射の擬同型性を得る。
規約：射影モデル構造は証明内でのみ用い、大域 instance を追加しない。
使われ方：指定された底を保つ実 dg 写像空間の相対ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]
variable {P Q X Y : Complex A} (i : P ⟶ Q) (p : X ⟶ Y)

/-- 概要：元の内部 Hom の固定底引き戻し。
方針：後合成と前合成の実 pullback を選ぶ。
規約：二つの射影の順序は Hom(P,X)、Hom(Q,Y)。
使われ方：相対内部 Hom 比較の標的。 -/
abbrev complexPullbackHomTarget : Complex A :=
  pullback (homPostcompose P p) (homPrecompose i Y)

/-- 概要：元の Hom(Q,X) から固定底 pullback への比較射。
方針：前合成・後合成の交換則で実 pullback に持ち上げる。
規約：閉構造 complexMonoidalClosed の内部 Hom を使う。
使われ方：射影 trivial cofibration に対する相対全射擬同型。 -/
def complexPullbackHom : homComplex A Q X ⟶ _root_.SerrePositivity.ComplexLimits.complexPullbackHomTarget i p :=
  pullback.lift (homPrecompose i X) (homPostcompose Q p)
    (homPostcompose_precompose A i p).symm

/-- 概要：比較射の第一射影は元の前合成。
方針：pullback の持ち上げの第一射影則。
規約：同じ P、X と i を保つ。
使われ方：固定底の制限射との照合。 -/
@[reassoc (attr := simp)]
lemma complexPullbackHom_fst : _root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.fst _ _ =
    homPrecompose i X := pullback.lift_fst _ _ _

/-- 概要：比較射の第二射影は元の後合成。
方針：pullback の持ち上げの第二射影則。
規約：同じ Q、p を保つ。
使われ方：指定底への構造射との照合。 -/
@[reassoc (attr := simp)]
lemma complexPullbackHom_snd : _root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.snd _ _ =
    homPostcompose Q p := pullback.lift_snd _ _ _

/-- 概要：射影 cofibration と次数別全射の pullback-Hom は次数別全射。
方針：引き戻しの元を次数付きの可換平方として、各成分で持ち上げる。
規約：cofibration の擬同型性はここでは不要。
使われ方：固定底の相対 fibration。 -/
lemma complexPullbackHom_projectiveFibration
    (hi : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) := by
  have (k : ℤ) : Epi (p.f k) := (ModuleCat.epi_iff_surjective _).mpr (hp k)
  intro n z
  let a : Homogeneous P X n := (pullback.fst (homPostcompose P p) (homPrecompose i Y)).f n z
  let b : Homogeneous Q Y n := (pullback.snd (homPostcompose P p) (homPrecompose i Y)).f n z
  have hab : (homPostcompose P p).f n a = (homPrecompose i Y).f n b :=
    congrArg (fun f : _root_.SerrePositivity.ComplexLimits.complexPullbackHomTarget i p ⟶ homComplex A P Y => f.f n z)
      (pullback.condition (f := homPostcompose P p) (g := homPrecompose i Y))
  let s (k l : ℤ) (h : k + n = l) :
      CommSq (a.v k l h) (i.f k) (p.f l) (b.v k l h) := ⟨by
    simpa only [homPostcompose_apply, homPrecompose_apply, Cochain.comp_zero_cochain_v,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
      congrArg (fun c => c.v k l h) hab⟩
  have (k l : ℤ) (h : k + n = l) : (s k l h).HasLift :=
    ((_root_.SerrePositivity.ComplexLimits.projectiveCofibration_component_lifting i hi k (p.f l)).sq_hasLift (s k l h))
  let w : Homogeneous Q X n := Cochain.mk (fun k l h => (s k l h).lift)
  refine ⟨w, ?_⟩
  apply Types.ext_of_isPullback
    (IsPullback.map ((eval (ModuleCat.{u} A) (.up ℤ) n) ⋙ forget (ModuleCat.{u} A))
      (IsPullback.of_hasPullback (homPostcompose P p) (homPrecompose i Y)))
  · change ((_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.fst _ _).f n) w = a
    rw [_root_.SerrePositivity.ComplexLimits.complexPullbackHom_fst, homPrecompose_apply]
    apply Cochain.ext
    intro k l h
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, w, Cochain.mk_v] using
      (s k l h).fac_left
  · change ((_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.snd _ _).f n) w = b
    rw [_root_.SerrePositivity.ComplexLimits.complexPullbackHom_snd, homPostcompose_apply]
    apply Cochain.ext
    intro k l h
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, w, Cochain.mk_v] using
      (s k l h).fac_right

/-- 概要：射影 trivial cofibration の pullback-Hom は擬同型。
方針：前合成の鎖ホモトピー同値と trivial fibration の引き戻しから二対三を使う。
規約：p に条件を課さず、同じ実 pullback と比較射を扱う。
使われ方：固定底相対射の弱同値性。 -/
lemma complexPullbackHom_quasiIso
    (hi : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i) (hq : QuasiIso i) :
    QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.ProjectiveHomotopyInverse.projectiveTrivialCofibration_homotopyEquiv i hi hq
  have hpre (T : Complex A) : QuasiIso (homPrecompose i T) := by
    rw [← he]
    exact (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyEquiv e T).quasiIso_hom
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have : Fibration (homPrecompose i Y) :=
    ⟨_root_.SerrePositivity.HomRestriction.homPrecompose_projectiveFibration i hi Y⟩
  have : WeakEquivalence (homPrecompose i Y) := ⟨hpre Y⟩
  have : WeakEquivalence (pullback.fst (homPostcompose P p) (homPrecompose i Y)) :=
    inferInstance
  have : QuasiIso (pullback.fst (homPostcompose P p) (homPrecompose i Y)) :=
    (mem_quasiIso_iff _).mp (show WeakEquivalence
      (pullback.fst (homPostcompose P p) (homPrecompose i Y)) from inferInstance).mem
  have : QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p ≫ pullback.fst _ _) := by
    rw [_root_.SerrePositivity.ComplexLimits.complexPullbackHom_fst]
    exact hpre X
  exact quasiIso_of_comp_right _ (pullback.fst (homPostcompose P p) (homPrecompose i Y))

/-- 概要：射影 trivial cofibration と全射の固定底 pullback-Hom は全射擬同型。
方針：成分の持ち上げと同じ比較射の擬同型性を合わせる。
規約：モデル圏 instance を入力に要求しない。
使われ方：実 pullback を保つ相対ホーン充填への供給。 -/
lemma complexPullbackHom_trivialFibration
    (hi : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp i) (hq : QuasiIso i)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) ∧ QuasiIso (_root_.SerrePositivity.ComplexLimits.complexPullbackHom i p) :=
  ⟨_root_.SerrePositivity.ComplexLimits.complexPullbackHom_projectiveFibration i p hi hp, _root_.SerrePositivity.ComplexLimits.complexPullbackHom_quasiIso i p hi hq⟩

end SerrePositivity.ComplexLimits
