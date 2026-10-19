module
public import SerrePositivity.KST.ProExcision.CentralMultiplicationEquiv
public import SerrePositivity.KST.ProExcision.IntegerUnitizationIdealIso
public import SerrePositivity.KST.ProExcision.UnitizationMapInjective

/-!
# 実 aI の標準核イデアルと元の標準核イデアルの加法同型

概要：次数ごとに単射な中心元の実乗法を標準単位化の実核イデアルへ移す。
方針：既存の実核イデアル同型と実中心乗法同型を合成する。
規約：KST Proposition 4.14 の非可換再記述。環同型とはしない。
使われ方：実 aI→I のアフィン包含を実乗法へ因子化する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：単射な中心乗法による二つの実標準核イデアルの加法同型。
方針：元の非単位環との実加法同型を介して実乗法像へ移す。
規約：KST Proposition 4.14、各次数の実非零因子条件。
使われ方：実 aI のアフィン包含のファイバーの実同型。 -/
def NonUnitalSimplicialRing.centralIdealKernelAddEquiv (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x))
    (k : SimplexCategoryᵒᵖ) :
    integerUnitizationIdeal (I.obj k) ≃+ integerUnitizationIdeal ((I.centralIdeal a ha).obj k) :=
  (integerUnitizationIdealAddEquiv (I.obj k)).symm.trans
    ((centralMultiplicationAddEquiv (I.vertexValue a k) (ha k) (hinj k)).trans
      (integerUnitizationIdealAddEquiv ((I.centralIdeal a ha).obj k)))

/-- 概要：実核イデアル同型の包含後の値は実右乗法。
方針：実単位化の第一・第二成分を評価し、核条件と中心性を使う。
規約：KST Proposition 4.14、Lemma 4.16 の φ(x)=xa と一致する。
使われ方：実相対包含を既証明の実右乗法に因子化する。 -/
lemma NonUnitalSimplicialRing.centralIdealKernelAddEquiv_inclusion
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x))
    (k : SimplexCategoryᵒᵖ) (x : integerUnitizationIdeal (I.obj k)) :
    integerUnitizationMap ((I.centralIdealInclusion a ha).app k)
        (I.centralIdealKernelAddEquiv a ha hinj k x) =
      x.val * (I.vertexValue a k : Unitization ℤ (I.obj k)) := by
  apply Unitization.ext
  · change 0 = x.val.fst * 0
    exact (mul_zero _).symm
  · rw [integerUnitizationMap_snd, Unitization.snd_mul]
    change I.vertexValue a k * x.val.snd =
      x.val.fst • I.vertexValue a k + (0 : ℤ) • x.val.snd + x.val.snd * I.vertexValue a k
    have hx := (mem_integerUnitizationIdeal (I.obj k) x.val).mp x.property
    rw [hx, zero_smul, zero_smul, zero_add, zero_add]
    exact ha k x.val.snd

/-- 概要：実中心核イデアル同型は全ての係数の面・退化と可換。
方針：第二成分を元の非単位環へ忘れ、実指定元の自然性と乗法保存を使う。
規約：KST Proposition 4.14。使われ方：実単体的ベクトル群同型への束ね。 -/
lemma NonUnitalSimplicialRing.centralIdealKernelAddEquiv_natural
    (I : NonUnitalSimplicialRing.{u}) (a : I.obj (op ⦋0⦌))
    (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x))
    {k l : SimplexCategoryᵒᵖ} (φ : k ⟶ l) (x : integerUnitizationIdeal (I.obj k)) :
    idealCoefficientAddHom _ _ (integerUnitizationMap ((I.centralIdeal a ha).map φ))
        (integerUnitizationMap_ideal ((I.centralIdeal a ha).map φ))
        (I.centralIdealKernelAddEquiv a ha hinj k x) =
      I.centralIdealKernelAddEquiv a ha hinj l
        (idealCoefficientAddHom _ _ (integerUnitizationMap (I.map φ))
          (integerUnitizationMap_ideal (I.map φ)) x) := by
  apply Subtype.ext
  apply Unitization.ext
  · change (integerUnitizationMap ((I.centralIdeal a ha).map φ) _).fst = 0
    rw [integerUnitizationMap_fst]
    rfl
  · change (integerUnitizationMap ((I.centralIdeal a ha).map φ) _).snd = _
    rw [integerUnitizationMap_snd]
    apply Subtype.ext
    change I.map φ (I.vertexValue a k * x.val.snd) =
      I.vertexValue a l * (integerUnitizationMap (I.map φ) x.val).snd
    rw [integerUnitizationMap_snd, map_mul, I.vertexValue_natural]

/-- 概要：実中心核イデアル同型を各成分に適用した実ベクトル加法同型。
方針：実成分同型と逆同型を全座標に適用する。
規約：KST Proposition 4.14。使われ方：実行・列アフィン比較のファイバー同型。 -/
def NonUnitalSimplicialRing.centralIdealKernelVectorAddEquiv (I : NonUnitalSimplicialRing.{u})
    (a : I.obj (op ⦋0⦌)) (ha : ∀ k, IsCentralElement (I.vertexValue a k))
    (hinj : ∀ k, Function.Injective (fun x : I.obj k ↦ I.vertexValue a k * x))
    (n : ℕ) (k : SimplexCategoryᵒᵖ) :
    (Fin n → integerUnitizationIdeal (I.obj k)) ≃+
      (Fin n → integerUnitizationIdeal ((I.centralIdeal a ha).obj k)) where
  toFun v i := I.centralIdealKernelAddEquiv a ha hinj k (v i)
  invFun v i := (I.centralIdealKernelAddEquiv a ha hinj k).symm (v i)
  left_inv v := by funext i; exact (I.centralIdealKernelAddEquiv a ha hinj k).left_inv (v i)
  right_inv v := by funext i; exact (I.centralIdealKernelAddEquiv a ha hinj k).right_inv (v i)
  map_add' v w := by funext i; exact map_add (I.centralIdealKernelAddEquiv a ha hinj k) (v i) (w i)

end SerrePositivity.KST.ProExcision
