module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：path の形状変数を始点へ収縮し、族のパラメータを保持する。
方針：区間の単調な最小値の収縮を形状変数と時刻に適用する。
規約：時刻零で始点、時刻一で元の path。
使われ方：底を固定した path の全空間の変形 retract。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：形状と時刻を収縮して元のパラメータを残す射。
方針：時刻と形状に標準区間の収縮を使う。
規約：時刻は最も右の変数。使われ方：内部 Hom の族のホモトピー。 -/
def intervalShapeContraction (T : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (T ⊗ (Δ[1] : SSet.{u})) ⟶ (Δ[1] : SSet.{u}) ⊗ T :=
  lift (lift (snd Δ[1] (T ⊗ Δ[1]) ≫ snd T Δ[1]) (fst Δ[1] (T ⊗ Δ[1])) ≫
    prismFirstContraction 1) (snd Δ[1] (T ⊗ Δ[1]) ≫ fst T Δ[1])

/-- 概要：時刻零では全 path の形状を始点に固定する。
方針：収縮の零成分を全単体で計算する。
規約：族のパラメータは保持。使われ方：定値 path の切断との一致。 -/
lemma intervalShapeContraction_zero (T : SSet.{u}) :
    (Δ[1] ◁ (SSet.ι₀ : T ⟶ T ⊗ (Δ[1] : SSet.{u}))) ≫ intervalShapeContraction T =
      snd (Δ[1] : SSet.{u}) T ≫ prismEndpoint 0 T := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    rfl
  · rfl

/-- 概要：時刻一では元の形状と族に戻る。
方針：収縮の一成分を全単体で計算する。
規約：恒等射そのもの。使われ方：変形 retract の終端。 -/
lemma intervalShapeContraction_one (T : SSet.{u}) :
    (Δ[1] ◁ (SSet.ι₁ : T ⟶ T ⊗ (Δ[1] : SSet.{u}))) ≫ intervalShapeContraction T =
      𝟙 ((Δ[1] : SSet.{u}) ⊗ T) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    rfl
  · rfl

/-- 概要：形状の収縮は族のパラメータを変えない。
方針：第二射影を計算する。
規約：全時刻で厳密に一致。使われ方：底射の保持。 -/
lemma intervalShapeContraction_projection (T : SSet.{u}) :
    intervalShapeContraction T ≫ snd (Δ[1] : SSet.{u}) T =
      snd (Δ[1] : SSet.{u}) (T ⊗ (Δ[1] : SSet.{u})) ≫ fst T (Δ[1] : SSet.{u}) :=
  lift_snd _ _

end SerrePositivity.InfinityCategories.F2
