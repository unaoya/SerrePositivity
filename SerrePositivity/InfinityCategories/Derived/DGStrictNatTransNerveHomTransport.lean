module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNerveWhiskerHom
/-!
概要：元の厳密二経路比較の nerve 像を、入力の同じ変換と出力の恒等へ同定する。
方針：全厳密変換の型付き比較と nerve の前後合成を接続する。
規約：頂点だけの一致で代用しない。使われ方：指定分解比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
lemma dgStrictNatTransNerveHom_heq (R : Type u) [CommRing R] (C E : Type v)
    [DGCategory R C] [DGCategory R E] {F G F' G' : DGFunctor R C E}
    (η : StrictNatTrans F G) (θ : StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (hη : HEq η θ) :
    HEq (dgStrictNatTransNerveHom R C E η) (dgStrictNatTransNerveHom R C E θ) := by
  subst F' G'
  cases eq_of_heq hη
  rfl
end SerrePositivity.InfinityCategories
