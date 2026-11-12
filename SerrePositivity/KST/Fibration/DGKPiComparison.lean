module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.KST.LocalizingInvariants.SpectrumBFPiTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-! # 固定 dg K の辺と元の S• スペクトルの整数 π 作用

固定界面の頂点・辺の等号だけを使い、同じ K の辺を元の BF 対象へ輸送する。
局所化性や fiber 四角形を仮定しない。工程 (c)(d) の実射の照合に使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

local instance : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

variable (A : Type u) [CommRing A] {P Q : PerfDGInput.{u, v} A}

/-- 固定 K の同じ辺を、固定頂点比較で元の BF 対象間の辺として表示する。 -/
def dgKNormalizedEdge (f : P ⟶ Q) :
    Sp.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum A P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum A Q)) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).ofEq
    (dgKInputK_vertex A P) (dgKInputK_vertex A Q)

/-- 頂点を照合した実 K 辺は、元の S• BF 射の辺そのもの。 -/
lemma dgKNormalizedEdge_eq (f : P ⟶ Q) :
    dgKNormalizedEdge A f = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap A f) := by
  apply SSet.Edge.ext
  exact dgKInputK_edge A f

/-- 同じ辺のホモトピー類も、元の BF 射の類を回収する。 -/
lemma dgKNormalizedEdge_hom (f : P ⟶ Q) :
    SSet.Truncated.HomotopyCategory.homMk (dgKNormalizedEdge A f).toTruncated =
      SpectrumHo.hom (dgKInputSpectrumMap A f) := by
  rw [dgKNormalizedEdge_eq]
  rfl

/-- 実 K 辺の整数 π 作用を元の BF 群へ輸送すると、同じ BF 射の作用になる。 -/
theorem dgKNormalizedEdge_bfPiMap (f : P ⟶ Q) (j : ℤ) :
    SpectrumHo.bfPiMap
      (SSet.Truncated.HomotopyCategory.homMk (dgKNormalizedEdge A f).toTruncated) j =
        CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j) := by
  rw [dgKNormalizedEdge_hom]
  exact SpectrumHo.bfPiMap_hom _ j

/-- 元の BF 群との比較は、固定 K の同じ辺の整数 π 作用に対して可換する。 -/
theorem dgKNormalizedEdge_piComparison (f : P ⟶ Q) (j : ℤ) :
    (SpectrumHo.piFunctor j).map
        (SSet.Truncated.HomotopyCategory.homMk (dgKNormalizedEdge A f).toTruncated) ≫
      (SpectrumHo.piComparison (dgKInputSpectrum A Q) j).hom =
        (SpectrumHo.piComparison (dgKInputSpectrum A P) j).hom ≫
          CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j) := by
  rw [dgKNormalizedEdge_hom]
  exact SpectrumHo.piComparison_naturality _ j

/-- 固定 K の実頂点における π を、同じ S• BF 群に比較する。 -/
def dgKPiComparison (P : PerfDGInput.{u, v} A) (j : ℤ) :
    (SpectrumHo.piFunctor j).obj
        (HomotopyCategory.mk ((dgKInputK A).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P))) ≅
      CommGrpCat.of (OmegaSpectrum.homotopyGroup (dgKInputSpectrum A P) j) :=
  (SpectrumHo.piFunctor j).mapIso
    (eqToIso (congrArg HomotopyCategory.mk (dgKInputK_vertex A P))) ≪≫
      SpectrumHo.piComparison (dgKInputSpectrum A P) j

/-- 実際の K 辺の作用は、実頂点での比較に関して元の BF 射の作用と可換する。 -/
theorem dgKPiComparison_naturality (f : P ⟶ Q) (j : ℤ) :
    (SpectrumHo.piFunctor j).map
        (Truncated.HomotopyCategory.homMk
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated)) ≫
      (dgKPiComparison A Q j).hom =
        (dgKPiComparison A P j).hom ≫
          CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (dgKInputK_vertex A P) (dgKInputK_vertex A Q)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated)
    (dgKNormalizedEdge A f).toTruncated rfl
  have hn := dgKNormalizedEdge_piComparison A f j
  have ht' := congrArg
    (fun m => eqToHom (congrArg HomotopyCategory.mk (dgKInputK_vertex A P)) ≫ m) ht
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at ht'
  have hm := congrArg ((SpectrumHo.piFunctor j).map) ht'
  simp only [Functor.map_comp] at hm
  simp only [dgKPiComparison, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [← Category.assoc, hm, Category.assoc, hn]
  exact (Category.assoc _ _ _).symm

/-- 固定 K 辺の全射性は、同じ S• BF 射の整数 π の全射性と同値。
零次への適用が工程 (c) の具体的 cofinality 条件になる。 -/
theorem dgKPiMap_surjective_iff (f : P ⟶ Q) (j : ℤ) :
    Function.Surjective ((SpectrumHo.piFunctor j).map
      (Truncated.HomotopyCategory.homMk
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgKInputK A)).toTruncated))).hom ↔
      Function.Surjective (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j) := by
  have hn := dgKPiComparison_naturality A f j
  have hP := ConcreteCategory.bijective_of_isIso (dgKPiComparison A P j).hom
  have hQ := ConcreteCategory.bijective_of_isIso (dgKPiComparison A Q j).hom
  constructor
  · intro hs y
    obtain ⟨y', hy⟩ := hQ.2 y
    obtain ⟨x, hx⟩ := hs y'
    refine ⟨(dgKPiComparison A P j).hom.hom x, ?_⟩
    have he := congrArg (fun m => m.hom x) hn
    exact he.symm.trans ((congrArg (dgKPiComparison A Q j).hom.hom hx).trans hy)
  · intro hs y
    obtain ⟨z, hz⟩ := hs ((dgKPiComparison A Q j).hom.hom y)
    obtain ⟨x, hx⟩ := hP.2 z
    refine ⟨x, hQ.1 ?_⟩
    have he := congrArg (fun m => m.hom x) hn
    exact he.trans
      ((congrArg (OmegaSpectrum.homotopyMap (dgKInputSpectrumMap A f) j) hx).trans hz)

end SerrePositivity.KST.Fibration
