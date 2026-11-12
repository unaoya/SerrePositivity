module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHomEquiv
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FlagIso

/-!
# coherent pinched Hom と解像の右随伴の同型

概要：固定次数の評価の同値を単体集合の同型にし、逆向きの標準 Hom 射を解像の比較射に同定する。
方針：両方向の自然性で次数ごとの同値をまとめ、標準単体の評価式を適用する。
規約：二段の ULift は F1 の右随伴と coherent nerve の宇宙を合わせるもの。
使われ方：HA 1.3.1.17、Kerodon Corollary 4.6.7.16（Tag 01LQ） の比較射の位相的な部分への接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：実際の coherent pinched Hom は標準 Hom の解像の右随伴と同型である。
方針：評価と逆構成の両逆則を各次数の同型とし、評価の自然性でまとめる。
規約：coherent nerve の宇宙 max(u,v) での同型。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の一般の解像の比較への帰着。 -/
def resolutionHomIso (x y : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y ≅
      SSet.uliftFunctor.{v, u}.obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)) :=
  NatIso.ofComponents (fun d ↦
    { hom := ↾fun s ↦ ULift.up (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap s))
      inv := ↾fun φ ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomEquiv x y d.unop.len).symm φ.down.down
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro s
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomEquiv_symm_map s
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro φ
        apply ULift.ext
        apply ULift.ext
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomMap_equiv_symm φ.down.down }) (by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap_reindex s α.unop)

/-- 概要：解像の同型の順方向は旗での実際の評価を返す。
方針：次数ごとの同型の定義を評価する。
規約：右随伴と外側の宇宙の二段の持ち上げを明示する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ） の具体的な比較射の照合。 -/
lemma resolutionHomIso_hom_app {x y : ClosedCategory R D} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) _⦋n⦌) :
    (resolutionHomIso x y).hom.app (Opposite.op ⦋n⦌) s =
      ULift.up (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap s)) := rfl

/-- 概要：標準 Hom から coherent pinched Hom への射は解像の標準比較射に一致する。
方針：全単体での評価の射影公式と解像の比較射の単体公式を照合する。
規約：射の等式であり、頂点やホモトピー類だけの一致ではない。
使われ方：HA 1.3.1.17 の比較の同値性を解像の射影へ接続する可換式。 -/
lemma standardHomToCoherentPinched_resolutionHomIso (x y : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched (R := R) (D := D) x y ≫ (resolutionHomIso x y).hom =
      SSet.uliftFunctor.{v, u}.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)) := by
  apply CategoryTheory.NatTrans.ext
  funext d
  rcases d with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply ULift.ext
  change ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardCoherentPinchedSimplex σ.down)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)).app
      (Opposite.op ⦋n⦌) σ.down
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison_app, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionHomMap_standard]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
