module
public import SerrePositivity.KST.SConstruction.TracedBFTriplePathDiamond
public import SerrePositivity.KST.SConstruction.CoherentSimplexFaceActions

/-! # 三入力 BF 四面体の全三面の Path 作用の厳密な回収
概要：保存した三つの元の合成面の、全 Path の豊穣作用を同じ四面体から回収する。
方針：面の全二単体の等号と、面の再添字による全豊穣前合成を合わせる。
規約：全写像を依存等号で照合し、対象表示の差を成分の一致で代用しない。
使われ方：同じ Path 挿入二単体の辺を既存の全 BF 比較面へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedTripleFaceSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 前二射の元の面の全 Path 作用は、同じ四面体の全作用の面制限。 -/
lemma monicKTracedCoherentTriple_first_face_mapping (a b : Fin 3) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} 3 a b ≫
      (monicKTracedCoherentTripleData F f g h).simplex.map
        (.mk (ULift.up ((3 : Fin 4).succAbove a)))
        (.mk (ULift.up ((3 : Fin 4).succAbove b))))
      ((monicKTracedCoherentComposition F f g).simplex.map
        (.mk (ULift.up a)) (.mk (ULift.up b))) :=
  coherentSimplexFaceMapping_heq _ _ _ (monicKTracedCoherentTriple_first_face F f g h) a b

/-- 後二射の元の面の全 Path 作用も、同じ四面体の全作用の面制限。 -/
lemma monicKTracedCoherentTriple_second_face_mapping (a b : Fin 3) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} 0 a b ≫
      (monicKTracedCoherentTripleData F f g h).simplex.map
        (.mk (ULift.up ((0 : Fin 4).succAbove a)))
        (.mk (ULift.up ((0 : Fin 4).succAbove b))))
      ((monicKTracedCoherentComposition F g h).simplex.map
        (.mk (ULift.up a)) (.mk (ULift.up b))) :=
  coherentSimplexFaceMapping_heq _ _ _ (monicKTracedCoherentTriple_second_face F f g h) a b

/-- 右結合の元の面の全 Path 作用も、同じ四面体の全作用の面制限。 -/
lemma monicKTracedCoherentTriple_right_face_mapping (a b : Fin 3) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} 2 a b ≫
      (monicKTracedCoherentTripleData F f g h).simplex.map
        (.mk (ULift.up ((2 : Fin 4).succAbove a)))
        (.mk (ULift.up ((2 : Fin 4).succAbove b))))
      ((monicKTracedCoherentComposition F f (g ≫ h)).simplex.map
        (.mk (ULift.up a)) (.mk (ULift.up b))) :=
  coherentSimplexFaceMapping_heq _ _ _ (monicKTracedCoherentTriple_right_face F f g h) a b

/-- 生成された第四面の全作用も同じ四面体の面制限であり、独立に選び直さない。 -/
lemma monicKTracedCoherentTriple_generated_face_mapping (a b : Fin 3) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap.{u} 1 a b ≫
      (monicKTracedCoherentTripleData F f g h).simplex.map
        (.mk (ULift.up ((1 : Fin 4).succAbove a)))
        (.mk (ULift.up ((1 : Fin 4).succAbove b))))
      ((monicKTracedCoherentTripleGeneratedLeft F f g h).simplex.map
        (.mk (ULift.up a)) (.mk (ULift.up b))) :=
  coherentSimplexFaceMapping_heq _ _ _
    (monicKTracedCoherentTripleGeneratedLeft_face F f g h).symm a b

end SerrePositivity.KST.SConstruction
