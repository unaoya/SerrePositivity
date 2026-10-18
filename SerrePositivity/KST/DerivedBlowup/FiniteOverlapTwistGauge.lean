module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistScalar
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTransitionScalar
public import SerrePositivity.KST.DerivedBlowup.RestrictedForwardScalar
public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeFunctor

/-!
概要：KST §3.1 の O(m) の単元 cocycle を係数 dg 圏の自己関手にする。
方針：局所 scalar 自己同型とチャート遷移の半線形性で合成保存を証明する。
規約：係数図式と大域加群の模型を保ち、その Hom を可逆に重み付けする。
使われ方：構造図式加群の制限による大域 O(m) の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 三つの局所係数環の Hom と共通基底環の tensor を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
/-- 概要：指定捻り自己同型は係数遷移後の積と可換。
方針：純 tensor 上で半線形性・局所双線形性・単元 cocycle を順に適用する。
規約：KST §3.1。使われ方：O(m) の Hom gauge の合成条件。 -/
theorem finiteOverlapTwistScalar_comp (a : I → R) {T U V : FiniteOverlapIndex I}
    (h : T ≤ U) (g : U ≤ V) (m : ℤ) :
    ((finiteOverlapTwistScalar R a h m).hom ⊗ₘ (finiteOverlapTwistScalar R a g m).hom) ≫
        diagramAlgebraMul ((finiteOverlapDGAlgebraDiagram R a).map (homOfLE g)) =
      diagramAlgebraMul ((finiteOverlapDGAlgebraDiagram R a).map (homOfLE g)) ≫
        (finiteOverlapTwistScalar R a (h.trans g) m).hom := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (MonObj.mul (X := ((finiteOverlapDGAlgebraDiagram R a).obj V).X)).f n
      ((((finiteOverlapDGAlgebraDiagram R a).map (homOfLE g)).hom ⊗ₘ 𝟙 _).f n
        (((finiteOverlapTwistScalar R a h m).hom ⊗ₘ
          (finiteOverlapTwistScalar R a g m).hom).f n
          (ιTensorObj ((finiteOverlapDGAlgebraDiagram R a).obj U).X
            ((finiteOverlapDGAlgebraDiagram R a).obj V).X p q n hn (x ⊗ₜ[R] y)))) =
    ((finiteOverlapTwistScalar R a (h.trans g) m).hom.f n)
      ((MonObj.mul (X := ((finiteOverlapDGAlgebraDiagram R a).obj V).X)).f n
        ((((finiteOverlapDGAlgebraDiagram R a).map (homOfLE g)).hom ⊗ₘ 𝟙 _).f n
          (ιTensorObj ((finiteOverlapDGAlgebraDiagram R a).obj U).X
            ((finiteOverlapDGAlgebraDiagram R a).obj V).X p q n hn (x ⊗ₜ[R] y))))
  rw [tensorMap_apply, tensorMap_apply, tensorMap_apply]
  change forward R (D := FiniteOverlapBaseKoszulObject R a (finiteOverlapIndexPivot V) V.val)
      ((((finiteOverlapBaseDGTransition R a (finiteOverlapIndexPivot U)
        (finiteOverlapIndexPivot V) g (finiteOverlapIndexPivot_mem U)).map .point .point).f p)
        (((finiteOverlapTwistScalar R a h m).hom.f p) x))
      (((finiteOverlapTwistScalar R a g m).hom.f q) y) hn =
    ((finiteOverlapTwistScalar R a (h.trans g) m).hom.f n)
      (forward R (D := FiniteOverlapBaseKoszulObject R a (finiteOverlapIndexPivot V) V.val)
        ((((finiteOverlapBaseDGTransition R a (finiteOverlapIndexPivot U)
          (finiteOverlapIndexPivot V) g (finiteOverlapIndexPivot_mem U)).map .point .point).f p) x)
        y hn)
  rw [finiteOverlapTwistScalar_hom_apply, finiteOverlapTwistScalar_hom_apply,
    finiteOverlapTwistScalar_hom_apply, finiteOverlapBaseDGTransition_smul]
  let z : (homObject (FiniteOverlapVertexRing R V)
      (FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot V) V.val) .point .point).X p :=
    (((finiteOverlapBaseDGTransition R a (finiteOverlapIndexPivot U)
      (finiteOverlapIndexPivot V) g (finiteOverlapIndexPivot_mem U)).map .point .point).f p) x
  let w : (homObject (FiniteOverlapVertexRing R V)
    (FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot V) V.val) .point .point).X q := y
  change forward R (D := FiniteOverlapBaseKoszulObject R a (finiteOverlapIndexPivot V) V.val)
      (finiteOverlapChartMap R (finiteOverlapIndexPivot U) (finiteOverlapIndexPivot V)
        g (finiteOverlapIndexPivot_mem U)
        (finiteOverlapTwistUnit R h m : FiniteOverlapVertexRing R U) • z)
      ((finiteOverlapTwistUnit R g m : FiniteOverlapVertexRing R V) • w) hn =
    (finiteOverlapTwistUnit R (h.trans g) m : FiniteOverlapVertexRing R V) •
      (show (homObject (FiniteOverlapVertexRing R V)
        (FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot V) V.val) .point .point).X n from
        forward R (D := FiniteOverlapBaseKoszulObject R a (finiteOverlapIndexPivot V) V.val) z w hn)
  rw [restrictedForward_eq R (FiniteOverlapVertexRing R V),
    restrictedForward_eq R (FiniteOverlapVertexRing R V), localForward_smul]
  have hc := congrArg Units.val (finiteOverlapTwistUnit_comp R h g m)
  simp only [Units.val_mul, Units.coe_map] at hc
  rw [mul_comm] at hc
  exact congrArg (fun b : FiniteOverlapVertexRing R V =>
    b • forward (FiniteOverlapVertexRing R V)
      (D := FiniteOverlapKoszulObject R a (finiteOverlapIndexPivot V) V.val) z w hn) hc

/-- 概要：全有限重なりの O(m) に対応する証明済み Hom gauge。
方針：局所 scalar 自己同型を恒等律と合成保存の証明で束ねる。
規約：KST §3.1。使われ方：実際の係数 dg 自己関手の入力。 -/
def finiteOverlapTwistGauge (a : I → R) (m : ℤ) :
    DiagramHomGauge (finiteOverlapDGAlgebraDiagram R a) where
  scale h := finiteOverlapTwistScalar R a h m
  scale_id T := finiteOverlapTwistScalar_id R a T m
  scale_comp h g := finiteOverlapTwistScalar_comp R a h g m

/-- 概要：O(m) の Hom 重み付けによる実際の大域係数 dg 自己関手。
方針：全ての整合性を証明した gauge を既存の自己関手構成へ渡す。
規約：KST §3.1。使われ方：構造加群を引き戻して大域捻りを定義する。 -/
def finiteOverlapTwistDGFunctor (a : I → R) (m : ℤ) :=
  diagramGaugeDGFunctor (finiteOverlapDGAlgebraDiagram R a) (finiteOverlapTwistGauge R a m)

end SerrePositivity.KST.DerivedBlowup
