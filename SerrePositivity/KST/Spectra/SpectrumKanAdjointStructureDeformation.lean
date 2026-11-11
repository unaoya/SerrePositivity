module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointBoundaryStructure

/-!
概要：非零境界の構造区間を垂直化した際の、同じ選択済み区間への実変形を回収する。
方針：元の収縮の持ち上げの choose_spec から、両端固定と指定射影を同時に取り出す。
規約：垂直区間を選び直さない。使われ方：輸送正方形と相対帰納正方形の共通辺の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]
  (c : B ⟶ pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence))
  (H : ∀ n, KanAdjointBoundaryHomotopy X Y φ j c n)
  (s : ∀ n, KanAdjointBoundaryCoordinate X Y φ j c n (H n))

/-- 同じ垂直区間への変形を、元の両端固定条件と収縮そのものへの射影つきで回収する。 -/
def kanAdjointBoundaryStructureDeformation (n : ℕ)
    (P : KanAdjointBoundaryStructurePath X Y φ j c H s n)
    (K : KanAdjointBoundaryStructureContraction X Y φ j c H s n P) :
    { V : SSet.Homotopy P.path
        (kanAdjointBoundaryVerticalStructurePath X Y φ j c H s n P K).path //
      (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ P.path ∧
      V.h ≫ (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.mappingPre j (KanSequence.signedLoopTail Y.toKanSequence)).app
          (n + 1))).right = K.homotopy.h } := by
  let hex := PointedMapping.exists_vertical_path_of_projection_contraction _
    (mappingPre_level_horn_rlp j (KanSequence.signedLoopTail Y.toKanSequence) (n + 1))
    P K.homotopy K.boundary
  exact ⟨hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

end SerrePositivity.KST.Spectra.RawSpectrumMapping
