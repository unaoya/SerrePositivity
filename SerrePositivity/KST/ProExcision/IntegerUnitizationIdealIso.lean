module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialRing

/-!
# 元の非単位環と標準単位化の核イデアルの自然な同型

概要：非単位環の加法群を整数単位化の核イデアルと自然に同定する。
方針：包含と第二成分の互いの逆を使う。
規約：KST Lemma 4.16 の単位化模型の型の同定。
使われ方：元の I の列ベクトルと標準の実群模型の列ベクトルを結び付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable (I : Type u) [NonUnitalRing I]

/-- 概要：元の非単位環の加法群と整数単位化の核イデアルの加法同型。
方針：標準包含と第二成分で互いの逆を与える。
規約：KST 4.16、I の可換性は不要。
使われ方：標準のイデアル模型に追加の表現仮定がないことを実同型で示す。 -/
def integerUnitizationIdealAddEquiv : I ≃+ integerUnitizationIdeal I where
  toFun x := ⟨(x : Unitization ℤ I), inr_mem_integerUnitizationIdeal I x⟩
  invFun x := x.val.snd
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    apply Unitization.ext
    · exact ((mem_integerUnitizationIdeal I x.val).mp x.property).symm
    · rfl
  map_add' x y := by
    apply Subtype.ext
    exact Unitization.inr_add ℤ x y

/-- 概要：標準核イデアルへの同型は非単位環準同型に自然。
方針：整数単位化の拡張が標準包含と可換であることを使う。
規約：KST 4.16 の (I,a) の射。
使われ方：元の非単位単体環の面・退化との整合。 -/
lemma integerUnitizationIdealAddEquiv_natural {J : Type v} [NonUnitalRing J] (f : I →ₙ+* J) (x : I) :
    idealCoefficientAddHom (integerUnitizationIdeal I) (integerUnitizationIdeal J)
        (integerUnitizationMap f) (integerUnitizationMap_ideal f) (integerUnitizationIdealAddEquiv I x) =
      integerUnitizationIdealAddEquiv J (f x) := by
  apply Subtype.ext
  exact integerUnitizationMap_inr f x

/-- 概要：元の I の列と核イデアルの列の加法同型。
方針：各成分に標準同型を適用する。
規約：KST 4.16 の M_{n,1}(I) の型の同定。
使われ方：標準の単位化模型の実列を元の非単位環の列と読む。 -/
def integerUnitizationIdealVectorAddEquiv (ι : Type v) : (ι → I) ≃+ (ι → integerUnitizationIdeal I) where
  toFun v i := integerUnitizationIdealAddEquiv I (v i)
  invFun v i := (integerUnitizationIdealAddEquiv I).symm (v i)
  left_inv v := by funext i; exact (integerUnitizationIdealAddEquiv I).left_inv (v i)
  right_inv v := by funext i; exact (integerUnitizationIdealAddEquiv I).right_inv (v i)
  map_add' v w := by funext i; exact map_add (integerUnitizationIdealAddEquiv I) (v i) (w i)

end SerrePositivity.KST.ProExcision
