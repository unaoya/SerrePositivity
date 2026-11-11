module
public import SerrePositivity.KST.SConstruction.TracedBFTripleWhiskers

/-! # 元の全 BF 二単体を保持する三入力の実合成三角形対
概要：同じ BF 写像空間内の元の二経路を、同じ実対角辺を持つ二つの実合成三角形にする。
方針：全四辺を元の比較辺へ合わせ、元の二単体と共通面から同じ実三角形対を回収する。
規約：三角形の全二単体の像を保持する。独立に指定した第四面との一致は主張しない。
使われ方：元の raw 高次 prism と指定比較面を合わせる三入力の実二次元データ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedTripleCompositionSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の全二単体を持つ、元の四辺と共通対角辺の実合成三角形対の保存データ。 -/
def monicKTracedCoherentTripleCompositionDiamondData :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.triangleDiamondCompositionData
    (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f)
      (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedSpectrumMap F (f ≫ g ≫ h))
      (monicKTracedCoherentComposition F f (g ≫ h)))
    (monicKTracedCoherentTripleFirstWhisker F f g h)
    (monicKTracedCoherentTripleGeneratedEdge F f g h)
    (monicKTracedCoherentTripleSecondWhisker F f g h)
    (monicKTracedCoherentTripleEdgeDiamond F f g h)

/-- 同じ BF 写像空間において、元の二経路を同じ実対角辺へ合成する実三角形対。 -/
def monicKTracedCoherentTripleCompositionDiamond :=
  (monicKTracedCoherentTripleCompositionDiamondData F f g h).val

/-- 第一の実合成三角形全体は、元の第一 Path 二単体の表示移送の像そのもの。 -/
lemma monicKTracedCoherentTripleCompositionDiamond_first_image :
    (monicKTracedCoherentTripleCompositionDiamond F f g h).first.simplex =
      (eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
        (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex :=
  (monicKTracedCoherentTripleCompositionDiamondData F f g h).property.1.trans
    (monicKTracedCoherentTripleDiamond_first_image F f g h)

/-- 第二の実合成三角形全体も、元の第二 Path 二単体の同じ表示移送の像そのもの。 -/
lemma monicKTracedCoherentTripleCompositionDiamond_second_image :
    (monicKTracedCoherentTripleCompositionDiamond F f g h).second.simplex =
      (eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
        (monicKTracedCoherentTripleSecondPathTriangle F f g h).simplex :=
  (monicKTracedCoherentTripleCompositionDiamondData F f g h).property.2.trans
    (monicKTracedCoherentTripleDiamond_second_image F f g h)

/-- 共通の実対角辺も元の全二単体の同じ対角面そのもの。 -/
lemma monicKTracedCoherentTripleCompositionDiamond_diagonal :
    (monicKTracedCoherentTripleCompositionDiamond F f g h).diagonal.edge =
      (OmegaSpectrum.mappingSpace (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z))).δ 1
        ((eqToHom (monicKTracedCoherentTripleMappingSpace_eq F f g h)).app (Opposite.op ⦋2⦌)
          (monicKTracedCoherentTripleFirstPathTriangle F f g h).simplex) :=
  (monicKTracedCoherentTripleCompositionDiamond F f g h).first.d₁.symm.trans
    (congrArg ((OmegaSpectrum.mappingSpace (kOmegaSpectrum (F.obj w))
      (kOmegaSpectrum (F.obj z))).δ 1)
      (monicKTracedCoherentTripleCompositionDiamond_first_image F f g h))

end SerrePositivity.KST.SConstruction
