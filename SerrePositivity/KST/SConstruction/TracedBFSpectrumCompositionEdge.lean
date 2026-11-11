module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeBFBoundaryFaces
public import SerrePositivity.KST.SConstruction.PointFamilyHomotopyEdge
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.KST.Spectra.CoherentNerve

/-! # 既存 BF 境界を表す実スペクトル射と元の合成比較辺
概要：既存の同じ BF 境界を通常のスペクトル射へ戻し、元の合成比較円柱を実豊穣辺にする。
方針：写像空間の頂点同値を使い、豊穣合成の零単体公式で両端を厳密に照合する。
規約：新しい境界射を選ばず、元の比較辺の全区間を保持する。
使われ方：入力二射の元の BF 合成比較を coherent nerve の三面に配置する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedBoundarySpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I}

/-- 既存の同じ BF 境界頂点を表す、実際の通常のスペクトル射。 -/
def monicKTracedSpectrumMap (f : x ⟶ y) : kOmegaSpectrum (F.obj x) ⟶ kOmegaSpectrum (F.obj y) :=
  (SimplicialCategory.homEquiv' _ _).symm (SSet.yonedaEquiv (monicKPrismTracedBFBoundary F f))

/-- 実スペクトル射の頂点は元の同じ BF 境界そのもの。 -/
lemma monicKTracedSpectrumMap_vertex (f : x ⟶ y) :
    SimplicialCategory.homEquiv' _ _ (monicKTracedSpectrumMap F f) =
      SSet.yonedaEquiv (monicKPrismTracedBFBoundary F f) :=
  Equiv.apply_symm_apply _ _

/-- 実スペクトル射の合成頂点も、元の二つの BF 境界を実合成した同じ頂点。 -/
lemma monicKTracedSpectrumMap_comp_vertex (f : x ⟶ y) (g : y ⟶ z) :
    SimplicialCategory.homEquiv' _ _ (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g) =
      SSet.yonedaEquiv
        (lift (monicKPrismTracedBFBoundary F f) (monicKPrismTracedBFBoundary F g) ≫
          OmegaSpectrum.mappingComposition (kOmegaSpectrum (F.obj x))
            (kOmegaSpectrum (F.obj y)) (kOmegaSpectrum (F.obj z))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp, monicKTracedSpectrumMap_vertex, monicKTracedSpectrumMap_vertex]
  rfl

/-- 元の BF 境界円柱全体を保つ、合成射の頂点から二射の実合成頂点への豊穣辺。 -/
def monicKTracedSpectrumCompositionEdge (f : x ⟶ y) (g : y ⟶ z) :
    (OmegaSpectrum.mappingSpace (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj z))).Edge
      (SimplicialCategory.homEquiv' _ _ (monicKTracedSpectrumMap F (f ≫ g)))
      (SimplicialCategory.homEquiv' _ _
        (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g)) :=
  (pointFamilyHomotopyEdge (monicKPrismTracedBFCompositionBoundary F f g)).ofEq
    (monicKTracedSpectrumMap_vertex F (f ≫ g)).symm
    (monicKTracedSpectrumMap_comp_vertex F f g).symm

/-- 頂点表示を移しても、豊穣比較辺全体は元の同じ BF 境界円柱の実制限。 -/
lemma monicKTracedSpectrumCompositionEdge_map (f : x ⟶ y) (g : y ⟶ z) :
    SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge =
      lift (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (monicKPrismTracedBFCompositionBoundary F f g).h :=
  pointFamilyHomotopyEdge_map _

end SerrePositivity.KST.SConstruction
