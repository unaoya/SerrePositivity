module
public import SerrePositivity.InfinityCategories.F1B.RestrictedDeformationHomotopy
/-!
概要：変形による局所化を、包含の像を含む頂点全部分圏へ制限する。
方針：同じ辺条件と元の比較の持ち上げを、全標的の前合成同値へ渡す。
規約：全部分圏の対象を元の局所対象と同一視しない。使われ方：K-flat 入力の局所化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
/-- 元の辺条件を、指定写像の実一次単体に沿って引き戻す。 -/
def preimageEdges {A X : SSet.{u}} (j : A ⟶ X) (W : Set (X _⦋1⦌)) : Set (A _⦋1⦌) :=
  {s | j.app (Opposite.op ⦋1⦌) s ∈ W}
/-- 元の辺を反転する関手は、前合成後も引き戻した辺条件を反転する。 -/
lemma InvertsEdges.precomp {A X D : SSet.{u}} {L : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hL : InvertsEdges L W) (j : A ⟶ X) :
    InvertsEdges (j ≫ L) (preimageEdges j W) := by
  intro s hs
  have hi := hL hs
  exact (isInvertibleEdge_congr (X := D)
    (e := (edgeOfSimplex s).map ((truncation 2).map (j ≫ L)))
    (f := (edgeOfSimplex (j.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map L)) rfl).mpr hi
variable {X D : SSet.{u}} (P : X _⦋0⦌ → Prop) (L : X ⟶ D) (I : D ⟶ X)
  (hI : ∀ x, P (I.app (Opposite.op ⦋0⦌) x)) (W : Set (X _⦋1⦌))
/-- 制限した包含と分解の合成は、元の同じ全関手同型で恒等に比較される。 -/
def deformationRestrictedRetractIso (e : FunctorIso (I ≫ L) (𝟙 D)) :
    FunctorIso
      (fullSubcomplexLift P I hI ≫ ((fullSubcomplexOnVertices X P).ι ≫ L)) (𝟙 D) := by
  simpa only [← Category.assoc, fullSubcomplexLift_ι] using! e
/-- 制限した変形比較の各成分は、同じ引き戻し辺条件を満たす。 -/
lemma deformationRestrictedHomotopy_vertex_mem
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (x : (fullSubcomplexOnVertices X P : SSet) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (deformationRestrictedHomotopy P L I hI H) x).edge ∈
      preimageEdges (fullSubcomplexOnVertices X P).ι W := by
  change (simplicialHomotopyVertexEdge
    (deformationRestrictedHomotopy P L I hI H) x).edge.val ∈ W
  rw [deformationRestrictedHomotopy_vertex_val]
  exact hH x.val
/-- 指定した全部分圏からの制限分解も、全反転関手 ∞ 圏との明示的前合成同値を与える。 -/
def deformationRestrictedLocalizationEquivalence
    (hL : InvertsEdges L W) (e : FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (Y : SSet.{u}) [Quasicategory Y] :
    QCatEquivalence ((ihom D).obj Y)
      (invertingFunctors (fullSubcomplexOnVertices X P : SSet) Y
        (preimageEdges (fullSubcomplexOnVertices X P).ι W) : SSet) :=
  deformationLocalizationPrecompositionEquivalence _ _ _
    (hL.precomp (fullSubcomplexOnVertices X P).ι)
    (deformationRestrictedRetractIso P L I hI e)
    (deformationRestrictedHomotopy P L I hI H)
    (deformationRestrictedHomotopy_vertex_mem P L I hI W H hH) Y
include hI in
/-- 包含の像を含む全部分圏からの同じ分解は、引き戻した辺に関する局所化。 -/
lemma isLocalization_of_restricted_deformation
    (hL : InvertsEdges L W) (e : FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W) :
    IsLocalization ((fullSubcomplexOnVertices X P).ι ≫ L)
      (preimageEdges (fullSubcomplexOnVertices X P).ι W) := by
  refine ⟨hL.precomp (fullSubcomplexOnVertices X P).ι, fun Y _ => ?_⟩
  exact (deformationRestrictedLocalizationEquivalence P L I hI W hL e H hH Y).isQCatEquivalence
end SerrePositivity.InfinityCategories
