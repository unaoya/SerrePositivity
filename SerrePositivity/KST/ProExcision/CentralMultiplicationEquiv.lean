module
public import SerrePositivity.KST.ProExcision.NonUnitalCentralIdeal

/-!
# 非零因子である中心元の実乗法像との加法同型

概要：中心元の乗法が単射であるとき、元の非単位環と実両側イデアル aI を加法的に同定する。
方針：実乗法像への準同型の単射性と全射性を直接証明する。
規約：KST Proposition 4.14 の非可換版。環同型とは主張しない。
使われ方：実アフィン相対包含を実乗法写像へ因子化する。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {I : Type u} [NonUnitalRing I]

/-- 概要：中心元の実乗法像への加法群準同型。
方針：元 x を実イデアル内の a x に送る。
規約：KST Proposition 4.14、非可換係数。
使われ方：実乗法が単射のときの加法同型の正方向。 -/
def centralMultiplicationAddHom (a : I) (ha : IsCentralElement a) :
    I →+ centralMultiplicationIdeal a ha where
  toFun x := ⟨a * x, (mem_centralMultiplicationIdeal a ha _).mpr ⟨x, rfl⟩⟩
  map_zero' := Subtype.ext (mul_zero a)
  map_add' x y := Subtype.ext (mul_add a x y)

/-- 概要：単射な中心元の実乗法像と元の加法群の実同型。
方針：実乗法像への準同型の単射性は仮定から、全射性は実像の表示から示す。
規約：KST Proposition 4.14 の次数ごとの非零因子条件。
使われ方：実アフィン包含のファイバーの因子化。 -/
def centralMultiplicationAddEquiv (a : I) (ha : IsCentralElement a)
    (hinj : Function.Injective (fun x : I ↦ a * x)) : I ≃+ centralMultiplicationIdeal a ha :=
  AddEquiv.ofBijective (centralMultiplicationAddHom a ha) ⟨
    fun x y h ↦ hinj (congrArg Subtype.val h), by
      intro x
      obtain ⟨y, hy⟩ := (mem_centralMultiplicationIdeal a ha x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩⟩

/-- 概要：実中心乗法同型の包含後の値は右乗法にも一致する。
方針：実同型の正方向と中心性を使う。
規約：KST Proposition 4.14 と Lemma 4.16 の φ(x)=xa の整合。
使われ方：包含の実相対写像を既証明の実右乗法へ移す。 -/
lemma centralMultiplicationAddEquiv_coe_right (a : I) (ha : IsCentralElement a)
    (hinj : Function.Injective (fun x : I ↦ a * x)) (x : I) :
    (centralMultiplicationAddEquiv a ha hinj x : I) = x * a := ha x

/-- 概要：実中心乗法同型は指定元を保つ実係数射に自然。
方針：実正方向の包含後の値に実準同型の乗法保存を適用する。
規約：KST Proposition 4.14 の (I,a) の実自然性。
使われ方：実単体的なファイバー同型への束ね。 -/
lemma centralMultiplicationAddEquiv_natural {J : Type v} [NonUnitalRing J]
    (f : I →ₙ+* J) (a : I) (b : J) (ha : IsCentralElement a) (hb : IsCentralElement b)
    (hinj : Function.Injective (fun x : I ↦ a * x))
    (hinj' : Function.Injective (fun x : J ↦ b * x)) (hab : f a = b) (x : I) :
    f (centralMultiplicationAddEquiv a ha hinj x : I) =
      (centralMultiplicationAddEquiv b hb hinj' (f x) : J) := by
  change f (a * x) = b * f x
  rw [map_mul, hab]

end SerrePositivity.KST.ProExcision
