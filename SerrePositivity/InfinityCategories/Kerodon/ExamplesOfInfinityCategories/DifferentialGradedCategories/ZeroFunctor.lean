module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-! # 零複体への定値 dg 関手と零自然変換

概要：複体 dg 圏で零対象に定値な dg 関手と、その両方向の厳密自然変換を作る。
方針：零対象を端点に持つ全次数 Hom の零性で関手則と自然性を検証する。
規約：HA Construction 1.3.1.6、HTT §1.2.12。使われ方：N7b の零対象への直接の錐の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：零複体に定値な複体 dg 圏の dg 関手。
方針：Hom 写像を零とし、終域 Hom 複体の零性で単位・合成の法則を示す。
規約：HTT §1.2.12、N7b。使われ方：全次数の零成分を持つ錐の構成。 -/
def constantZeroFunctor (Z : Complex A) (hZ : IsZero Z) : DGFunctor A (Complex A) (Complex A) where
  obj _ := Z
  map _ _ := 0
  map_id _ := (homComplex_isZero_tgt (P := Z) hZ).eq_of_tgt _ _
  map_comp _ _ _ := (homComplex_isZero_tgt (P := Z) hZ).eq_of_tgt _ _

/-- 概要：恒等 dg 関手から零定値関手への閉零成分の厳密自然変換。
方針：各成分を零とし、零終域への斉次射が零であることから自然性を得る。
規約：HA Construction 1.3.1.6、HTT §1.2.12。使われ方：零終対象への直接の錐。 -/
def toZeroStrict (Z : Complex A) (hZ : IsZero Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (DGFunctor.id (Complex A)) (constantZeroFunctor Z hZ) where
  app _ := 0
  naturality _ := (homogeneous_eq_zero_of_isZero_tgt hZ _).trans
    (homogeneous_eq_zero_of_isZero_tgt hZ _).symm

/-- 概要：零定値関手から恒等 dg 関手への閉零成分の厳密自然変換。
方針：各成分を零とし、零始域からの斉次射が零であることから自然性を得る。
規約：HA Construction 1.3.1.6、HTT §1.2.12 の双対。使われ方：零始対象からの直接の錐。 -/
def fromZeroStrict (Z : Complex A) (hZ : IsZero Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (constantZeroFunctor Z hZ) (DGFunctor.id (Complex A)) where
  app _ := 0
  naturality _ := (homogeneous_eq_zero_of_isZero_src hZ _).trans
    (homogeneous_eq_zero_of_isZero_src hZ _).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
