module

public import SerrePositivity.KST.Spectra.PointedCotensorFamilyNaturality
public import SerrePositivity.KST.Spectra.PointedCotensorStructureCoordinates
public import SerrePositivity.KST.Spectra.PointedVerticalPathFunctoriality

/-!
概要：自由パラメータ族を cotensor 値の射へ移しても、元の列の構造像を厳密に保つ。
方針：構造射の座標交換則を、同じ通常の族の指数頂点で評価する。
規約：族の全体の等式。使われ方：自由区間値の構造区間の終点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedCotensorCoordinates

/-- 同じ通常の族の構造像を移すと、cotensor 値へ移した射の構造像そのもの。 -/
lemma family_step (K : SSet.{u}) (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ)
    (a : K ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right) :
    PointedSimplicialSet.circle.{u} ◁ family a ≫
      (KanSequence.mapping (PointedObject.adjoin K) Y).sigma n =
    family (a ≫ (RawSpectrumMapping.pointedStep X Y n).right) := by
  apply ext
  rw [← PointedMapping.familyVertex_post, ← PointedMapping.VerticalPath.familyVertex_suspension,
    family_vertex]
  change (iso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).hom.app _
    ((RawSpectrumMapping.pointedStep X
      (KanSequence.mapping (PointedObject.adjoin K) Y) n).right.app _
        (PointedMapping.familyVertex (family a))) = _
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (PointedMapping.familyVertex (family a))) (natural_step K X Y n)
  simp only [NatTrans.comp_app_apply] at h
  erw [family_vertex a,
    ExponentialPaths.vertex_post a (RawSpectrumMapping.pointedStep X Y n).right] at h
  exact h

end SerrePositivity.KST.Spectra.PointedCotensorCoordinates
