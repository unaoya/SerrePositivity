module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSimplexPastingInputs
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
/-!
概要：指定transport比較による底変換の共役を、既存の単体切断の係数比較へ正規化する。
方針：元の初頂点制限の共役公式を使い、指定した中間同型だけを相殺する。
規約：HTT §3.3.2、Kerodon §5.6・Corollary 5.6.0.6（Tag 028T）の構成の法則。
  元のθ・βを保つ特殊化であり、別の同型を選ばない。
使われ方：P3-C1PNで指定νの射を元の切断図式の係数比較へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定したtransportの共役は、同じ単体切断係数の逆と指定端点比較の共役。 -/
@[cite HTT "3.3.2" (partial := special) "初頂点制限を通る指定transport底変換比較の正規化則。"]
lemma leftStraightening_baseChange_transport_normalized {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    let U := SSet.uliftFunctor.{u+1,u}
    let t := U.map (nerveMap (transportSimplexFunctor k))
    let q := pullback.snd p k
    let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
    let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
    let β := leftStraighteningInfinityDiagram_baseChangeIso p k
    let σp := (leftClassificationSimplexIso p).symm ≪≫ θp
    let σq := (leftClassificationSimplexIso q).symm ≪≫ θq
    (θp.precomp t).symm ≪≫
      diagramIsoCongr
        (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc]) rfl
        (β.precomp (U.map (transportSimplexFirstVertexMap D))) ≪≫ θq =
    (FunctorIso.precomp σp t).symm ≪≫ (simplexSectionBaseChangeCoefficient p k).symm ≪≫ σq := by
  dsimp only
  rw [leftStraightening_baseChange_simplex_normalized]
  apply Iso.ext
  simp only [functorIso_precomp_trans, functorIso_precomp_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
