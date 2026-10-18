module

public import SerrePositivity.KST.DerivedBlowup.AlgebraVertex
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST §3.1 の自己 Hom による一対象正規表示と元の局所模型の比較。
方針：Hom 恒等同型と元の対象の一意性で dg 準同値を示す。
規約：この比較は一般の一対象 dg 圏について構成する。
使われ方：正規表示で行う図式計算を元の Koszul チャートへ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded

variable {R : Type u} [CommRing R]

/-- 概要：元の dg 圏が指定した一点のみを持てば一対象表示の H⁰ 比較は本質的全射。
方針：任意の H⁰ 対象を対象の一意性によって指定点の像と同定する。
規約：KST §3.1。使われ方：局所正規表示の準同値の第二条件。 -/
theorem algebraVertexToOriginalEssSurj (D : Type v) [DGCategory R D] (x : D)
    (hx : ∀ y : D, y = x) : (algebraVertexToOriginal (R := R) D x).onHomotopy.EssSurj where
  mem_essImage Y := by
    refine ⟨(toHomotopy R (AlgebraVertex (dgEndMonoid R D x))).obj
      (ForgetEnrichment.of (Complex R) .point), ⟨eqToIso ?_⟩⟩
    change (toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x) = Y
    have hy : (ForgetEnrichment.of (Complex R) x : ClosedCategory R D) = Y.as :=
      congrArg (ForgetEnrichment.of (Complex R))
        (hx (ForgetEnrichment.to (Complex R) Y.as)).symm
    exact congrArg (fun Z : ClosedCategory R D => (toHomotopy R D).obj Z) hy

/-- 概要：一対象 dg 圏は自己 Hom の一対象正規表示と dg 準同値。
方針：Hom の恒等同型による擬同型性と H⁰ の本質的全射性を束ねる。
規約：KST §3.1。使われ方：局所 Koszul 模型の同じ代数の正規表示への接続。 -/
theorem algebraVertexToOriginalQuasiEquivalence (D : Type v) [DGCategory R D] (x : D)
    (hx : ∀ y : D, y = x) : QuasiEquivalence (algebraVertexToOriginal (R := R) D x) := by
  refine ⟨?_, algebraVertexToOriginalEssSurj (R := R) D x hx⟩
  intro i j
  change QuasiIso (𝟙 _)
  infer_instance

end SerrePositivity.KST.DerivedBlowup
