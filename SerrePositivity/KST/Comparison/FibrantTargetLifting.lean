module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Kan 基底上の fibration と局所化可逆な単射の持ち上げ

概要：局所化可逆な単射は、Kan 基底上の Kan fibration に対し左持ち上げ性を持つ。
方針：Kan な全空間へ厳密に延長し、基底上の誤差を相対ホモトピーで補正する。
規約：Segal 1974 Proposition 1.6 の貼り合わせの補助。基底の Kan 性を明示する。
使われ方：スライスの右随伴に対する局所化可逆性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/--
概要：局所化可逆な単射は Kan 基底上の Kan fibration に対して持ち上がる。
方針：全空間への延長後、基底への合成を単射上で固定したホモトピーで直す。
規約：Segal 1974 Proposition 1.6 の補助。基底が Kan であることを使う。
使われ方：スライスの写像空間の随伴を局所化へ移す。
-/
theorem localizedMono_lifting_fibrantTarget {A X E B : SSet.{u}}
    (i : A ⟶ X) [Mono i] (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) [SSet.KanComplex B] :
    HasLiftingProperty i p := by
  let : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  let : SSet.KanComplex E := isFibrant_of_fibration p
  have hE : SSet.modelCategoryQuillen.J.rlp (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := KanMonoStrictExtension.exists_extension i hE hi a
  let HA : SSet.Homotopy (i ≫ (g ≫ p)) (i ≫ b) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (KanActualHomotopy.refl (a ≫ p))
      (by rw [← Category.assoc, hg]) sq.w
  obtain ⟨H, hH⟩ := KanMonoRelativeHomotopy.exists_extension i hi hB (g ≫ p) b HA
  let HE : SSet.Homotopy (i ≫ g) a :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (KanActualHomotopy.refl a) hg.symm rfl
  have hHE : HE.h ≫ p = i ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
    rw [hH]
    dsimp only [HE, HA]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
    rfl
  obtain ⟨l, hl, V, _, hV⟩ := KanFibrationEndpointExtension.exists_from_zero p hp i g a HE H.h
    H.h₀.symm hHE
  refine ⟨⟨{ l := l, fac_left := hl, fac_right := ?_ }⟩⟩
  calc
    l ≫ p = (SSet.ι₁ ≫ V.h) ≫ p := by rw [V.h₁]
    _ = SSet.ι₁ ≫ H.h := by rw [Category.assoc, hV]
    _ = b := H.h₁

end SerrePositivity.KST.Comparison
