module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransHomotopyWhisker
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransNerveHom
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawTransport
/-!
概要：厳密 dg 変換の実 nerve 像と前後合成を、同じ全円柱で照合する。
方針：元の指定値と全 Hom 自然性を保持する実関手を使う。
規約：頂点成分の一致へ弱めない。使われ方：kernel の triangle・pentagon の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (B C D E : Type v)
  [DGCategory R B] [DGCategory R C] [DGCategory R D] [DGCategory R E]
  {F G : DGFunctor R C D}
/-- 同じ厳密 dg 変換の nerve 像は、後合成の全関手射と型付きで一致。 -/
lemma dgStrictNatTransNerveHom_postcomp_heq (η : StrictNatTrans F G) (Q : DGFunctor R D E) :
    HEq (dgStrictNatTransNerveHom R C E (dgStrictNatTransPostcomp η Q))
      ((SSet.mapHomotopyCategory ((ihom (dgNerve R C)).map (dgNerve.map Q))).map
        (dgStrictNatTransNerveHom R C D η)) := by
  rw [dgStrictNatTransNerveHom_spec, dgStrictNatTransNerveHom_spec]
  have hh := functorHomotopyHom_heq_of_raw_eq (dgStrictNatTransPostcomp η Q).homotopy
    (functorHomotopyPostcomp η.homotopy (dgNerve.map Q))
    (dgStrictNatTransPostcomp_homotopyMap η Q)
  exact hh.trans (heq_of_eq (functorHomotopyPostcomp_hom η.homotopy (dgNerve.map Q)))
/-- 同じ厳密 dg 変換の nerve 像は、前合成の全関手射と型付きで一致。 -/
lemma dgStrictNatTransNerveHom_precomp_heq (P : DGFunctor R B C) (η : StrictNatTrans F G) :
    HEq (dgStrictNatTransNerveHom R B D (dgStrictNatTransPrecomp P η))
      ((SSet.mapHomotopyCategory ((pre (dgNerve.map P)).app (dgNerve R D))).map
        (dgStrictNatTransNerveHom R C D η)) := by
  rw [dgStrictNatTransNerveHom_spec, dgStrictNatTransNerveHom_spec]
  have hh := functorHomotopyHom_heq_of_raw_eq (dgStrictNatTransPrecomp P η).homotopy
    (functorHomotopyPrecomp η.homotopy (dgNerve.map P))
    (dgStrictNatTransPrecomp_homotopyMap P η)
  exact hh.trans (heq_of_eq (functorHomotopyPrecomp_hom η.homotopy (dgNerve.map P)))
end SerrePositivity.InfinityCategories
