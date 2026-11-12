module
public import SerrePositivity.KST.SConstruction.DGFunctorHomElementFamily
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans

/-!
概要：元厳密 dg 自然変換を、全次数 Hom end の同じ閉零元へ送る。
方針：元全次数自然性を符号付き end の元に変え、全評価で閉性を判定する。
規約：元の閉零成分を保持する。使われ方：元 cone 零化の境界と全関手二単体。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] {F G : DGFunctor R D E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元厳密変換の全自然性は end の豊穣順自然性そのもの。
方針：次数零の Koszul 符号を消す。規約：全 Hom 次数を保持。
使われ方：同じ閉零成分の end への持ち上げ。 -/
lemma dgStrictNatTransEnd_naturality (x y : D) (p n : ℤ) (f : GradedHom R x y p)
    (hn : 0 + p = n) (hn' : p + 0 = n) :
    (0 * p).negOnePow • forward R ((F.map x y).f p f) (η.app y).val hn' =
      forward R (η.app x).val ((G.map x y).f p f) hn := by
  obtain rfl : n = p := by omega
  simpa only [compose, mul_zero, zero_mul, Int.negOnePow_zero, one_smul]
    using η.naturality f

/-- 概要：同じ厳密変換の成分を持つ end 内の次数零元。
方針：元全次数自然性で end に持ち上げる。
規約：元成分そのもの。使われ方：閉性と元零化境界の同定。 -/
def dgStrictNatTransEndElement : (dgFunctorHom R D E F G).X 0 :=
  dgFunctorHomElementFromFamily R D E F G 0 (fun x => (η.app x).val)
    (dgStrictNatTransEnd_naturality R D E η)

/-- 概要：元厳密変換の end 元は同じ元成分を厳密回収する。
方針：end 持ち上げの評価則を使用。
規約：成分を変更しない。使われ方：閉性と指定辺の照合。 -/
lemma dgStrictNatTransEndElement_π (x : D) :
    (dgFunctorHomπ R D E F G x).f 0 (dgStrictNatTransEndElement R D E η) =
      (η.app x).val :=
  dgFunctorHomElementFromFamily_π R D E F G 0 (fun x => (η.app x).val)
    (dgStrictNatTransEnd_naturality R D E η) x

/-- 概要：元厳密変換の end 元は全関手 Hom 内で閉じている。
方針：全対象評価の chain 性と元閉零成分を使用。
規約：対象別の閉性だけでなく end 内の微分等号。使われ方：指定閉辺。 -/
lemma dgStrictNatTransEndElement_closed :
    (dgFunctorHom R D E F G).d 0 1 (dgStrictNatTransEndElement R D E η) = 0 := by
  apply dgFunctorHomElement_ext R D E
  intro x
  have hc := congrArg (fun fm => fm (dgStrictNatTransEndElement R D E η))
    ((dgFunctorHomπ R D E F G x).comm 0 1).symm
  change (dgFunctorHomπ R D E F G x).f 1
      ((dgFunctorHom R D E F G).d 0 1 (dgStrictNatTransEndElement R D E η)) =
    (homObject R E (F.obj x) (G.obj x)).d 0 1
      ((dgFunctorHomπ R D E F G x).f 0 (dgStrictNatTransEndElement R D E η)) at hc
  rw [map_zero]
  exact hc.trans ((congrArg ((homObject R E (F.obj x) (G.obj x)).d 0 1)
    (dgStrictNatTransEndElement_π R D E η x)).trans (η.app x).property)

/-- 概要：元厳密変換を同じ全次数 Hom end の実閉零元として保持する。
方針：同じ持ち上げ元と実証した閉性を束ねる。
規約：全成分を保持。使われ方：元実関手圏 nerve 内の指定辺。 -/
def dgStrictNatTransEndCycle : zeroCycles (dgFunctorHom R D E F G) :=
  ⟨dgStrictNatTransEndElement R D E η, dgStrictNatTransEndElement_closed R D E η⟩

end SerrePositivity.KST.SConstruction
