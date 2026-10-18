module
public import SerrePositivity.KST.ProExcision.ConstructionA5Functoriality
public import SerrePositivity.KST.ProExcision.IdealColumnEquivariance

/-!
# 係数イデアルの変更による実列の写像

概要：イデアルを保つ環準同型は列ベクトルの加法群の写像を誘導し、右乗法と可換。
方針：各成分に係数準同型を適用し、加法・乗法の保存を使う。
規約：KST Lemma 4.16 の (I,a) に関する関手性。
使われ方：帰納ホモトピーの始域と P,Q,H の係数変更。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：イデアルを保つ環準同型のイデアル内への制限。
方針：所属条件を添えて加法群準同型にする。
規約：KST 4.16。使われ方：列の係数写像。 -/
def idealCoefficientAddHom (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') : J →+ J' where
  toFun x := ⟨f x, hf x x.property⟩
  map_zero' := by apply Subtype.ext; exact map_zero f
  map_add' x y := by apply Subtype.ext; exact map_add f (x : R) (y : R)

/-- 概要：イデアル内の列ベクトルの群の係数写像。
方針：各成分の加法群準同型を乗法タグへ移す。
規約：KST 4.16。使われ方：始域 Q の関手性。 -/
def idealVectorMap (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R') (ι : Type w)
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') :
    Multiplicative (ι → J) →* Multiplicative (ι → J') :=
  (show (ι → J) →+ (ι → J') from
    { toFun := fun v i ↦ idealCoefficientAddHom J J' f hf (v i)
      map_zero' := by funext i; exact map_zero (idealCoefficientAddHom J J' f hf)
      map_add' := by intro v w; funext i; exact map_add (idealCoefficientAddHom J J' f hf) (v i) (w i) }).toMultiplicative

/-- 概要：指定元を保つ係数写像はイデアル内の右乗法と可換。
方針：各成分で係数準同型の乗法保存を使う。
規約：KST 4.16、右乗法の順序を固定する。
使われ方：A.5 の第一入力 α の係数変更。 -/
lemma idealVectorRightHom_functorial (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R') (ι : Type w)
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : R) (a' : R') (ha : f a = a')
    (v : Multiplicative (ι → J)) :
    idealVectorRightHom J' ι a' (idealVectorMap J J' ι f hf v) =
      idealVectorMap J J' ι f hf (idealVectorRightHom J ι a v) := by
  change (fun i ↦ idealRightMultiplication J' a' (idealCoefficientAddHom J J' f hf (v.toAdd i))) =
    (fun i ↦ idealCoefficientAddHom J J' f hf (idealRightMultiplication J a (v.toAdd i)))
  funext i
  apply Subtype.ext
  change f (v.toAdd i : R) * a' = f ((v.toAdd i : R) * a)
  rw [map_mul, ha]

/-- 概要：実三角ブロック群の係数写像は周囲の行列の成分への係数写像。
方針：単位と部分群の写像の定義を評価する。
規約：KST 4.16。使われ方：φ、ψ、u の関手性の実成分計算。 -/
lemma triangularBlockGroupMap_val (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (g : triangularBlockGroup n m J) :
    ((triangularBlockGroupMap n m J J' f hf g).val : Matrix (Fin (n + m)) (Fin (n + m)) R') =
      (g.val : Matrix (Fin (n + m)) (Fin (n + m)) R).map f := rfl

end SerrePositivity.KST.ProExcision
