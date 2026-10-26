module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.UliftPiComparison
/-!
概要：全基点 π の宇宙比較は、元の実単体的射と可換する。
方針：標準単体の宇宙同型で球面代表の自然性を計算し、商へ渡す。
規約：基点とその像を明示し、群同型の選択を変えない。
使われ方：native 評価の実脚のチャートを追加宇宙から戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable {X Y : SSet.{u}}

lemma dgBarCompactPointedSimplexUp_naturality (φ : X ⟶ Y) {n : ℕ} {x : X _⦋0⦌}
    (f : X.PtSimplex n x) :
    dgBarCompactPointedSimplexUp.{u, v} (mapSimplex φ rfl f) =
      mapSimplex (x := ULift.up x) (y := ULift.up (φ.app _ x))
        ((SSet.uliftFunctor.{v, u}).map φ) rfl (dgBarCompactPointedSimplexUp.{u, v} f) := by
  apply RelativeMorphism.ext
  change (uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map (f.map ≫ φ) =
    ((uliftStdSimplexIso.{u, v} n).inv ≫ (SSet.uliftFunctor.{v, u}).map f.map) ≫
      (SSet.uliftFunctor.{v, u}).map φ
  rw [Functor.map_comp, Category.assoc]

lemma dgBarCompactUliftPiEquiv_naturality [KanComplex X] [KanComplex Y]
    (φ : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌) (a : KanHomotopyGroup X n x) :
    dgBarCompactUliftPiEquiv.{u, v} Y n (φ.app _ x) (KanHomotopyGroup.map φ rfl a) =
      KanHomotopyGroup.map (x := ULift.up x) (y := ULift.up (φ.app _ x))
        ((SSet.uliftFunctor.{v, u}).map φ) rfl (dgBarCompactUliftPiEquiv.{u, v} X n x a) := by
  induction a using Quotient.inductionOn with | h f => ?_
  change KanHomotopyGroup.mk (dgBarCompactPointedSimplexUp.{u, v} (mapSimplex φ rfl f)) =
    KanHomotopyGroup.mk (mapSimplex (x := ULift.up x) (y := ULift.up (φ.app _ x))
      ((SSet.uliftFunctor.{v, u}).map φ) rfl (dgBarCompactPointedSimplexUp.{u, v} f))
  exact congrArg KanHomotopyGroup.mk (dgBarCompactPointedSimplexUp_naturality φ f)

end SerrePositivity.InfinityCategories
