module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingAcyclic
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.RelativeMappingEdge

/-!
概要：同じ列の射影を持つ二つの BF 射を、全写像空間で射影に垂直な実区間で結ぶ。
方針：各段の単射への RLP を全 Hom の境界充填へ移し、指定両端を持ち上げる。
規約：段ごとのホモトピー類には弱めない。使われ方：fibration 置換単位の相対自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping
open RawSpectrumMapping

lemma rawVertex_ext (X : OmegaSpectrum.{u}) (Z : KanSequence.{u})
    {v w : (space X Z) _⦋0⦌}
    (h : ∀ n, (evaluation X Z n).app _ v = (evaluation X Z n).app _ w) : v = w := by
  apply (SSet.unitHomEquiv (space X Z)).symm.injective
  apply hom_ext X Z
  intro n
  apply (SSet.unitHomEquiv _).injective
  rw [unitHomEquiv_comp, unitHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h n

variable {X W : OmegaSpectrum.{u}} {Z : KanSequence.{u}}
  (c : KanSequence.Hom W.toKanSequence Z) (f g : X ⟶ W)

lemma post_vertex_eq (h : ∀ n, f.app n ≫ c.app n = g.app n ≫ c.app n) :
    (post X c).app (Opposite.op ⦋0⦌) (vertexOfHom f) =
      (post X c).app (Opposite.op ⦋0⦌) (vertexOfHom g) := by
  apply rawVertex_ext X Z
  intro n
  have hf := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (vertexOfHom f))
    (post_evaluation X c n)
  have hg := congrArg (fun k ↦ k.app (Opposite.op ⦋0⦌) (vertexOfHom g))
    (post_evaluation X c n)
  change (evaluation X Z n).app _ ((post X c).app _ (vertexOfHom f)) =
    (PointedObject.basedHomMap (X.level n).space (c.app n)).right.app _
      ((evaluation X W.toKanSequence n).app _ (vertexOfHom f)) at hf
  change (evaluation X Z n).app _ ((post X c).app _ (vertexOfHom g)) =
    (PointedObject.basedHomMap (X.level n).space (c.app n)).right.app _
      ((evaluation X W.toKanSequence n).app _ (vertexOfHom g)) at hg
  rw [hf, hg]
  change (PointedObject.basedHomMap (X.level n).space (c.app n)).right.app _
      ((OmegaSpectrum.evaluation X W n).app _ (vertexOfHom f)) =
    (PointedObject.basedHomMap (X.level n).space (c.app n)).right.app _
      ((OmegaSpectrum.evaluation X W n).app _ (vertexOfHom g))
  rw [vertexOfHom_evaluation, vertexOfHom_evaluation]
  let cn : (W.level n).space ⟶ (Z.level n).space := c.app n
  change (PointedObject.basedHomMap (X.level n).space cn).right.app _
      (pointedHomVertexEquiv _ _ (f.app n)) =
    (PointedObject.basedHomMap (X.level n).space cn).right.app _
      (pointedHomVertexEquiv _ _ (g.app n))
  exact (pointedHomVertexEquiv_post (f.app n) cn).trans
    ((congrArg (pointedHomVertexEquiv _ _) (h n)).trans
      (pointedHomVertexEquiv_post (g.app n) cn).symm)

structure RelativePath where
  path : (mappingSpace X W).Edge (vertexOfHom f) (vertexOfHom g)
  «over» : (post X c).app (Opposite.op ⦋1⦌) path.edge =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((post X c).app (Opposite.op ⦋0⦌) (vertexOfHom f)) 1

def relativePath (hc : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (c.app n).right)
    (h : ∀ n, f.app n ≫ c.app n = g.app n ≫ c.app n) : RelativePath c f g := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.relativeMappingEdge (post X c) (post_rlp X c hc)
    (vertexOfHom f) (vertexOfHom g) (post_vertex_eq c f g h)
  exact ⟨P.edge, P.over⟩

lemma RelativePath.over_hom (P : RelativePath c f g) :
    SSet.yonedaEquiv.symm P.path.edge ≫ post X c =
      SSet.const ((post X c).app (Opposite.op ⦋0⦌) (vertexOfHom f)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact P.over

end SerrePositivity.KST.LocalizingInvariants.FiberMapping
