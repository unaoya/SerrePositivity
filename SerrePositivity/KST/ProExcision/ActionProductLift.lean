module
public import SerrePositivity.KST.ProExcision.GroupHomology

/-!
# 半直積からの実準同型の組み立て

概要：基底・ファイバーの準同型と作用の交換則から半直積上の準同型を構成する。
方針：ファイバーを先に、基底を後に掛け、半直積の積と交換則を比較する。
規約：KST Claim 4.15 の実比較射。作用する元の次数ごとの可逆性を要求しない。
使われ方：三角ブロックと ĜL の基底を一つの一般線形半直積へ送る。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {G : Type u} {H : Type v} {K : Type w}
variable [Monoid G] [Monoid H] [Monoid K] [MulDistribMulAction G H]

/-- 概要：作用の交換則を満たす二つの実準同型から半直積の実準同型を構成する。
方針：h(x)f(g) の積を交換則と結合律で整理する。
規約：KST Claim 4.15。次数ごとの逆元の存在を要求しない。
使われ方：外部 ĜL と三角群の同時比較。 -/
def actionProductLift (f : G →* K) (h : H →* K)
    (hc : ∀ g x, h (g • x) * f g = f g * h x) : ActionProduct G H →* K where
  toFun x := h x.fiber * f x.base
  map_one' := by
    change h 1 * f 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change h (x.fiber * (x.base • y.fiber)) * f (x.base * y.base) =
      (h x.fiber * f x.base) * (h y.fiber * f y.base)
    rw [map_mul, map_mul]
    calc
      h x.fiber * h (x.base • y.fiber) * (f x.base * f y.base) =
          h x.fiber * (h (x.base • y.fiber) * f x.base) * f y.base := by
        simp only [mul_assoc]
      _ = h x.fiber * (f x.base * h y.fiber) * f y.base := by rw [hc]
      _ = _ := by simp only [mul_assoc]

/-- 概要：半直積の実準同型は基底上で指定された準同型に一致する。
方針：ファイバー成分が単位であることを使う。
規約：KST Claim 4.15。使われ方：相対項の基準射の可換性。 -/
lemma actionProductLift_section (f : G →* K) (h : H →* K)
    (hc : ∀ g x, h (g • x) * f g = f g * h x) :
    (actionProductLift f h hc).comp actionProductSection = f := by
  apply MonoidHom.ext
  intro g
  change h 1 * f g = f g
  rw [map_one, one_mul]

/-- 概要：半直積の実準同型はファイバー上で指定された準同型に一致する。
方針：基底成分が単位であることを使う。
規約：KST Claim 4.15。使われ方：右乗法の列の比較。 -/
lemma actionProductLift_fiber (f : G →* K) (h : H →* K)
    (hc : ∀ g x, h (g • x) * f g = f g * h x) :
    (actionProductLift f h hc).comp actionProductFiber = h := by
  apply MonoidHom.ext
  intro x
  change h x * f 1 = h x
  rw [map_one, mul_one]

end SerrePositivity.KST.ProExcision
