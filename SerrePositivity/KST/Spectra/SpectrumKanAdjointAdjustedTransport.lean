module

public import SerrePositivity.KST.Spectra.SquareRightAdjustment
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointSquareSeams

/-!
概要：元の段調整の輸送正方形の右辺を、同じ垂直構造区間へ直して三辺を保持する。
方針：保存済みの両端固定変形を指数辺の指定射影つき合成へ入力する。
規約：正方形全体の追加の境界射影は未主張。使われ方：相対帰納正方形への実際の接続。
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

/-- 元の同じ輸送正方形を、段調整の区間の間の実ホモトピーとして読む。 -/
def kanAdjointCanonicalTransportHomotopy (n : ℕ) :=
  (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.homotopy (kanAdjointCanonicalStageTransport X Y φ j n))

/-- 正規化した右辺への制限も、元の同じ輸送構造区間そのもの。 -/
lemma kanAdjointCanonicalTransportHomotopy_right (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointCanonicalTransportHomotopy X Y φ j n).h =
      (kanAdjointCanonicalStageStructurePath X Y φ j n).path := by
  have hr : SquareAdjustment.rightSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  change _ ≫ (_root_.SerrePositivity.KST.Spectra.ThreeEdgeTransport.square (kanAdjointCanonicalStageTransport X Y φ j n)) = _
  rw [hr, Category.assoc, ThreeEdgeTransport.square_finish, ← Category.assoc,
    lift_snd, Category.id_comp]
  rfl

/-- 元の垂直化変形を、輸送正方形の同じ右辺からの変形として読む。 -/
def kanAdjointCanonicalRightDeformation (n : ℕ) :
    SSet.Homotopy
      (SquareAdjustment.rightSide ≫ (kanAdjointCanonicalTransportHomotopy X Y φ j n).h)
      (kanAdjointCanonicalVerticalStructurePath X Y φ j n).path where
  h := (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h
  h₀ := (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h₀.trans
    (kanAdjointCanonicalTransportHomotopy_right X Y φ j n).symm
  h₁ := (kanAdjointCanonicalStructureDeformation X Y φ j n).val.h₁
  rel := by ext m ⟨⟨s, hs⟩, r⟩; exact hs.elim

/-- 同じ実変形は、元の正規化した右辺の両端を全区間で固定する。 -/
lemma kanAdjointCanonicalRightDeformation_boundary (n : ℕ) :
    (boundary 1).ι ▷ (Δ[1] : SSet.{u}) ≫
        (kanAdjointCanonicalRightDeformation X Y φ j n).h =
      fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫
        SquareAdjustment.rightSide ≫ (kanAdjointCanonicalTransportHomotopy X Y φ j n).h := by
  exact (kanAdjointCanonicalStructureDeformation_boundary X Y φ j n).trans
    (congrArg (fst (∂Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (boundary 1).ι ≫ ·)
      (kanAdjointCanonicalTransportHomotopy_right X Y φ j n).symm)

/-- 元の輸送正方形の三辺を保ち、右辺を同じ垂直構造区間に直した実正方形。 -/
def kanAdjointCanonicalAdjustedTransport (n : ℕ) :=
  SquareAdjustment.adjustRight (kanAdjointCanonicalTransportHomotopy X Y φ j n)
    (kanAdjointCanonicalRightDeformation X Y φ j n)
    (kanAdjointCanonicalRightDeformation_boundary X Y φ j n)

/-- 修正後の右辺は、相対帰納構成で使う同じ垂直構造区間そのもの。 -/
lemma kanAdjointCanonicalAdjustedTransport_right (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h =
      (kanAdjointCanonicalVerticalStructurePath X Y φ j n).path := by
  exact SquareAdjustment.adjustRight_right (kanAdjointCanonicalTransportHomotopy X Y φ j n)
    (kanAdjointCanonicalRightDeformation X Y φ j n)
    (kanAdjointCanonicalRightDeformation_boundary X Y φ j n)

/-- 修正後の左辺も、元の輸送正方形の同じ左辺を厳密に保持する。 -/
lemma kanAdjointCanonicalAdjustedTransport_left (n : ℕ) :
    SquareAdjustment.leftSide ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h =
      SquareAdjustment.leftSide ≫ (kanAdjointCanonicalTransportHomotopy X Y φ j n).h := by
  exact SquareAdjustment.adjustRight_left (kanAdjointCanonicalTransportHomotopy X Y φ j n)
    (kanAdjointCanonicalRightDeformation X Y φ j n)
    (kanAdjointCanonicalRightDeformation_boundary X Y φ j n)

/-- 右辺修正後、相対帰納正方形との共通辺は元の実区間そのものとして厳密に一致する。 -/
lemma kanAdjointCanonicalAdjustedTransport_relative_seam (n : ℕ) :
    SquareAdjustment.rightSide ≫ (kanAdjointCanonicalAdjustedTransport X Y φ j n).h =
      SquareAdjustment.leftSide ≫ (kanAdjointRelativeTracedStructureHomotopy X Y φ j n).h := by
  rw [kanAdjointCanonicalAdjustedTransport_right]
  have hl : SquareAdjustment.leftSide.{u} =
      CartesianMonoidalCategory.lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫
        stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u}) := by
    apply CartesianMonoidalCategory.hom_ext <;> rfl
  rw [hl, Category.assoc, kanAdjointRelativeTracedStructureHomotopy_start,
    ← Category.assoc, lift_snd, Category.id_comp]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
