module
public import SerrePositivity.KST.ProExcision.IntegerUnitizationIdealIso
public import SerrePositivity.KST.ProExcision.UnitizationOppositeDiagram

/-!
# 反対単位化の核イデアルの実加法比較

概要：反対係数環の整数核と元の整数核を実加法同型で結ぶ。
方針：元の非単位環との実同型と反対型の加法同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：列から行への実ベクトル比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable (J : Type u) [NonUnitalRing J]

/-- 概要：反対単位化の整数核と元の整数核の実加法同型。
方針：第二成分、反対型の unop、標準包含を合成する。
規約：SW92 §1.2、係数の乗法は反転する。
使われ方：実行列比較と整合する行・列の加法群の比較。 -/
def integerUnitizationIdealOpAddEquiv :
    integerUnitizationIdeal Jᵐᵒᵖ ≃+ integerUnitizationIdeal J :=
  (integerUnitizationIdealAddEquiv Jᵐᵒᵖ).symm.trans
    ((MulOpposite.opAddEquiv : J ≃+ Jᵐᵒᵖ).symm.trans (integerUnitizationIdealAddEquiv J))

/-- 概要：核イデアルの実加法比較は単位化の実反対環同型に一致する。
方針：第一成分は核条件で零、第二成分は定義で一致する。
規約：KST Proposition 4.14。使われ方：非可換な反対転置の行作用への移送。 -/
lemma integerUnitizationIdealOpAddEquiv_coe (x : integerUnitizationIdeal Jᵐᵒᵖ) :
    (integerUnitizationIdealOpAddEquiv J x : Unitization ℤ J) =
      MulOpposite.unop (integerUnitizationOpEquiv J x.val) := by
  apply Unitization.ext
  · change 0 = x.val.fst
    exact ((mem_integerUnitizationIdeal Jᵐᵒᵖ x.val).mp x.property).symm
  · rfl

/-- 概要：核イデアルの実反対比較は係数準同型に自然。
方針：周囲環に移し、単位化の実同型の自然性を使う。
規約：SW92 §1.2。使われ方：行と列の比較の全ての面・退化。 -/
lemma integerUnitizationIdealOpAddEquiv_natural {K : Type v} [NonUnitalRing K]
    (f : J →ₙ+* K) (x : integerUnitizationIdeal Jᵐᵒᵖ) :
    integerUnitizationIdealOpAddEquiv K
        (idealCoefficientAddHom (integerUnitizationIdeal Jᵐᵒᵖ)
          (integerUnitizationIdeal Kᵐᵒᵖ) (integerUnitizationMap (NonUnitalRingHom.op f))
          (integerUnitizationMap_ideal (NonUnitalRingHom.op f)) x) =
      idealCoefficientAddHom (integerUnitizationIdeal J) (integerUnitizationIdeal K)
        (integerUnitizationMap f) (integerUnitizationMap_ideal f)
        (integerUnitizationIdealOpAddEquiv J x) := by
  apply Subtype.ext
  change (integerUnitizationIdealOpAddEquiv K _ : Unitization ℤ K) =
    integerUnitizationMap f (integerUnitizationIdealOpAddEquiv J x)
  rw [integerUnitizationIdealOpAddEquiv_coe, integerUnitizationIdealOpAddEquiv_coe]
  exact congrArg MulOpposite.unop
    (congrArg (fun h : Unitization ℤ Jᵐᵒᵖ →+* (Unitization ℤ K)ᵐᵒᵖ ↦ h x.val)
      (integerUnitizationOpEquiv_natural f))

/-- 概要：反対核イデアル内の列と元の核イデアル内の行の実加法同型。
方針：各成分に実核イデアル同型を適用する。
規約：SW92 §1.2。使われ方：実半直積比較のファイバー部分。 -/
def integerUnitizationIdealOpVectorAddEquiv (ι : Type v) :
    (ι → integerUnitizationIdeal Jᵐᵒᵖ) ≃+ (ι → integerUnitizationIdeal J) where
  toFun v i := integerUnitizationIdealOpAddEquiv J (v i)
  invFun v i := (integerUnitizationIdealOpAddEquiv J).symm (v i)
  left_inv v := by funext i; exact (integerUnitizationIdealOpAddEquiv J).left_inv (v i)
  right_inv v := by funext i; exact (integerUnitizationIdealOpAddEquiv J).right_inv (v i)
  map_add' v w := by funext i; exact map_add (integerUnitizationIdealOpAddEquiv J) (v i) (w i)

end SerrePositivity.KST.ProExcision
