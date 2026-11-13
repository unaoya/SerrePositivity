module
public import SerrePositivity.KST.SConstruction.TracedBFTripleMappingSpace
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondTransport

/-! # 全四辺と同じ対角辺を保つ元の三入力 BF 比較の二単体
概要：元の二つの全 Path 二単体を、同じ元の BF 写像空間の実二単体へ束ねる。
方針：始終 Hom の表示等号で写し、元の全四辺と共通対角辺を同時に回収する。
規約：元の全二単体の像を保存し、新たな充填や二単体の選び直しをしない。
使われ方：生成された左面と元の指定左面を比較する実二次元 BF データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedTripleDiamondSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 同じ BF 写像空間の実二単体と、元の二つの全二単体の像そのものの等号。 -/
def monicKTracedCoherentTripleDiamondData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondTransportData (monicKTracedCoherentTripleMappingSpace_eq F f g h)
    (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex
    (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex _ _ _ _
    (monicKTracedCoherentTripleFirstLower_heq F f g h)
    (monicKTracedCoherentTripleSecondLower_heq F f g h)
    (monicKTracedCoherentTripleFirstUpper_heq F f g h)
    (monicKTracedCoherentTripleSecondUpper_heq F f g h)
    (monicKTracedCoherentTriplePathTriangles_diagonal F f g h)

/-- 元の同じ BF 写像空間の二つの実二単体。全四辺と全対角辺を厳密に保持する。 -/
def monicKTracedCoherentTripleDiamond :=
  (monicKTracedCoherentTripleDiamondData F f g h).val

/-- 第一 BF 二単体全体は、元の第一 Path 二単体の同じ表示移送の像そのもの。 -/
lemma monicKTracedCoherentTripleDiamond_first_image :
    (monicKTracedCoherentTripleDiamond F f g h).first =
      (eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
        (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex :=
  (monicKTracedCoherentTripleDiamondData F f g h).property.1

/-- 第二 BF 二単体全体も、元の第二 Path 二単体の同じ表示移送の像そのもの。 -/
lemma monicKTracedCoherentTripleDiamond_second_image :
    (monicKTracedCoherentTripleDiamond F f g h).second =
      (eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
        (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex :=
  (monicKTracedCoherentTripleDiamondData F f g h).property.2

end SerrePositivity.KST.SConstruction
