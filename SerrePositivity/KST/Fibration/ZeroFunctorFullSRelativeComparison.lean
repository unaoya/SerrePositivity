module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSKanFamily
public import SerrePositivity.KST.Fibration.VerdierNullContractionComparison
public import SerrePositivity.KST.Fibration.VerdierNullCoreKanComparison

/-!
概要：指定部分族を固定する零値関手比較を、全 S• 始域の実 Ex∞ 評価へ送る。
方針：元の零値族を全部分複体へ制限し、その制限 fiber の比較辺を全 Hom へ写す。
規約：元の二胞体の全パラメータと指定合成端を保持する。
使われ方：全 S• 上の商核円柱と指定 Verdier 上下二胞体の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 指定部分で等しい元の全零値族は、同じ全部分複体への制限後にも厳密に等しい。 -/
theorem zeroStableHomFamilyLift_restriction {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P Q : SSet.{u}}
    (i : P ⟶ Q) (f g : Q ⟶ (A ⟶[SSet.{u}] C))
    (hf : ∀ v, StableHomZeroVertex A C (f.app (Opposite.op ⦋0⦌) v))
    (hg : ∀ v, StableHomZeroVertex A C (g.app (Opposite.op ⦋0⦌) v))
    (hfg : i ≫ f = i ≫ g) :
    i ≫ zeroStableHomFamilyLift f hf = i ≫ zeroStableHomFamilyLift g hg := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj C.obj) _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex).ι).1
  rw [Category.assoc, zeroStableHomFamilyLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    Category.assoc, zeroStableHomFamilyLift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    ← Category.assoc, ← Category.assoc, hfg]

/-- 同じ制限 fiber の比較辺を、全 S• 始域の元の Ex∞ Hom へ写す。 -/
def zeroFunctorFullSRelativeComparison {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P Q : SSet.{u}}
    (i : P ⟶ Q) [Mono i] (f g : Q ⟶ (A ⟶[SSet.{u}] C))
    (hf : ∀ v, StableHomZeroVertex A C (f.app (Opposite.op ⦋0⦌) v))
    (hg : ∀ v, StableHomZeroVertex A C (g.app (Opposite.op ⦋0⦌) v))
    (hfg : i ≫ f = i ≫ g) :
    FixedRestrictionFunctorEdge i
      (zeroStableHomFamilyLift f hf ≫ zeroFunctorFullSKanFamily A C)
      (zeroStableHomFamilyLift g hg ≫ zeroFunctorFullSKanFamily A C) :=
  (contractibleRestrictionComparison i (zeroFunctorLocus_isContractibleKan A C)
    (zeroStableHomFamilyLift f hf) (zeroStableHomFamilyLift g hg)
    (zeroStableHomFamilyLift_restriction i f g hf hg hfg)).postcomp _

/-- 元の上下二胞体の全評価を、全 S• 始域のまま共有対角上で恒等の辺で結ぶ。 -/
def verdierNullHomFullSComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (zeroStableHomFamilyLift (verdierNullHomFamily d j) (verdierNullHomFamily_zero d j) ≫
        zeroFunctorFullSKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (zeroStableHomFamilyLift (verdierNullHomFamily d k) (verdierNullHomFamily_zero d k) ≫
        zeroFunctorFullSKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  zeroFunctorFullSRelativeComparison _ _ _ (verdierNullHomFamily_zero d j)
    (verdierNullHomFamily_zero d k) (verdierNullHomFamily_same_direct d j k)

/-- 元の核円柱と指定下側二胞体の全 S• 評価を、同じ実合成端を固定して結ぶ。 -/
def verdierNullContractionFullSComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (zeroStableHomFamilyLift (verdierNullContractionFamily d)
        (zeroEndPostcompFamily_zero_vertices _ _) ≫
        zeroFunctorFullSKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
      (zeroStableHomFamilyLift (verdierNullPathFamily d 1) (verdierNullPathFamily_zero d 1) ≫
        zeroFunctorFullSKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
          ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) := by
  apply zeroFunctorFullSRelativeComparison
  exact (zeroEndPostcompFamily_one _ _).trans
    ((congrArg SSet.yonedaEquiv.symm
      (stableHom_homEquiv'_ExactMap (verdierNullCompositeVertex d 1))).trans
        (verdierNullPathFamily_one d 1).symm)

/-- 全 S• 上の同じ相対比較の全評価円柱は、実合成端の全時刻で厳密に恒等。 -/
theorem verdierNullContractionFullSComparison_fixed (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 2)) ≫
        (verdierNullContractionFullSComparison d).prism =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        stdSimplex.δ (0 : Fin 2) ≫
          (zeroStableHomFamilyLift (verdierNullContractionFamily d)
            (zeroEndPostcompFamily_zero_vertices _ _) ≫
              zeroFunctorFullSKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
                ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)) :=
  (verdierNullContractionFullSComparison d).prism_restriction

/-- 同じ上下二胞体比較を内部評価し、全 S• 円柱の共有対角を厳密に固定する。 -/
def verdierNullHomFullSCylinderComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :=
  (verdierNullHomFullSComparison d j k).uncurryCoreKan

/-- 同じ核円柱比較を内部評価し、全 S• 円柱の実合成端を厳密に固定する。 -/
def verdierNullContractionFullSCylinderComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (verdierNullContractionFullSComparison d).uncurryCoreKan

/-- 全 S• 円柱の比較は、同じ実可逆辺による全関手同型である。 -/
def verdierNullContractionFullSCylinderIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (verdierNullContractionFullSCylinderComparison d).iso

end SerrePositivity.KST.Fibration
