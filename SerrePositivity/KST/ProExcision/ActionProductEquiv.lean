module
public import SerrePositivity.KST.ProExcision.GroupHomology

/-!
# 実同変な乗法同型による半直積の実同型

概要：基底とファイバーの実同型から半直積の実乗法同型を作る。
方針：二つの逆写像を成分ごとに与え、乗法保存に実同変性を使う。
規約：KST Appendix A、Proposition 4.14 の実比較。使われ方：非可換な行・列の比較。
-/
@[expose] public noncomputable section
universe u v w z
namespace SerrePositivity.KST.ProExcision

/-- 概要：基底とファイバーの実同変な同型による半直積の乗法同型。
方針：逆写像は二成分の逆で与え、積の第二成分に同変性を使う。
規約：KST App. A、各次数の群性も作用の可逆性も不要。
使われ方：反対転置による実アフィン比較。 -/
def actionProductMulEquiv {G : Type u} {H : Type v} {G' : Type w} {H' : Type z}
    [Monoid G] [Monoid H] [Monoid G'] [Monoid H']
    [MulDistribMulAction G H] [MulDistribMulAction G' H']
    (f : G ≃* G') (g : H ≃* H') (hc : ∀ a b, g (a • b) = f a • g b) :
    ActionProduct G H ≃* ActionProduct G' H' where
  toFun x := ⟨f x.base, g x.fiber⟩
  invFun y := ⟨f.symm y.base, g.symm y.fiber⟩
  left_inv x := by
    apply ActionProduct.ext
    · exact f.symm_apply_apply x.base
    · exact g.symm_apply_apply x.fiber
  right_inv y := by
    apply ActionProduct.ext
    · exact f.apply_symm_apply y.base
    · exact g.apply_symm_apply y.fiber
  map_mul' x y := by
    apply ActionProduct.ext
    · exact map_mul f x.base y.base
    · change g (x.fiber * (x.base • y.fiber)) = g x.fiber * (f x.base • g y.fiber)
      rw [map_mul, hc]

end SerrePositivity.KST.ProExcision
