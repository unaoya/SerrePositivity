module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces

/-! # 選んだ面のデータの貼り合わせ

概要：選んだ面で与えた整合的な単体は、その面の和からの写像になる。
方針：各単体を含む面を選び、面による分解で評価し、選択独立性で自然性を証明する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：slice 境界からの既知成分の入力。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：面による分解は前合成と可換。
方針：面の順序埋め込みの単射性で両辺を比較する。
規約：HA Proposition 1.3.1.10。使われ方：面を選んだ評価の自然性。 -/
lemma factor_δ_comp {l m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
    (hj : ∀ k, θ.toOrderHom k ≠ j) (α : ⦋l⦌ ⟶ ⦋m⦌) :
    SimplexCategory.factor_δ (α ≫ θ) j = α ≫ SimplexCategory.factor_δ θ j := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  apply j.succAboveOrderEmb.injective
  exact (congrArg (fun f => f.toOrderHom i)
    (SimplexCategory.factor_δ_spec (α ≫ θ) j (fun k => hj (α.toOrderHom k)))).trans
      (congrArg (fun f => f.toOrderHom (α.toOrderHom i))
        (SimplexCategory.factor_δ_spec θ j hj)).symm

/-- 概要：選んだ面の単体の族の整合性は、共通の順序写像への制限での一致。
方針：全ての共通の制限に対する等式として定義する。
規約：HA Proposition 1.3.1.10。使われ方：境界から来る二面の共通成分を貼り合わせる。 -/
def Compatible {n : ℕ} {X : SSet.{u}} (S : Finset (Fin (n + 2)))
    (s : ∀ j ∈ S, X _⦋n⦌) : Prop :=
  ∀ (m : ℕ) (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j l : Fin (n + 2))
    (hjS : j ∈ S) (hlS : l ∈ S)
    (_ : ∀ k, θ.toOrderHom k ≠ j) (_ : ∀ k, θ.toOrderHom k ≠ l),
    X.map (SimplexCategory.factor_δ θ j).op (s j hjS) =
      X.map (SimplexCategory.factor_δ θ l).op (s l hlS)

/-- 概要：部分境界の単体を、それを含む一つの選んだ面で評価する。
方針：所属条件から回避する頂点を選び、面の分解で制限する。
規約：HA Proposition 1.3.1.10。使われ方：貼り合わせ写像の各次数の値。 -/
def descValue {n m : ℕ} {X : SSet.{u}} (S : Finset (Fin (n + 2)))
    (s : ∀ j ∈ S, X _⦋n⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet) _⦋m⦌) : X _⦋m⦌ :=
  let j := x.property.choose
  X.map (SimplexCategory.factor_δ (SSet.stdSimplex.objEquiv x.val) j).op
    (s j x.property.choose_spec.1)

/-- 概要：整合的な族の評価は、それを含む任意の選んだ面で計算できる。
方針：定義で選ばれた面と指定された面の整合性を使う。
規約：HA Proposition 1.3.1.10。使われ方：貼り合わせの自然性と面への制限の確認。 -/
lemma descValue_cell {n m : ℕ} {X : SSet.{u}} (S : Finset (Fin (n + 2)))
    (s : ∀ j ∈ S, X _⦋n⦌) (hs : Compatible S s)
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) (hjS : j ∈ S)
    (hj : ∀ k, θ.toOrderHom k ≠ j) :
    descValue S s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell S θ j hjS hj) =
      X.map (SimplexCategory.factor_δ θ j).op (s j hjS) := by
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell.{u} S θ j hjS hj
  have h := hs m θ x.property.choose j x.property.choose_spec.1 hjS
    x.property.choose_spec.2 hj
  simpa only [descValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell, Equiv.apply_symm_apply] using h

/-- 概要：整合的な面の族を選んだ面の和からの単体的写像に貼り合わせる。
方針：各単体を含む面で評価し、共通の面での一致と面分解の前合成則で自然性を証明する。
規約：HA Proposition 1.3.1.10。使われ方：N7c の既知境界の入力写像。 -/
def desc {n : ℕ} {X : SSet.{u}} (S : Finset (Fin (n + 2)))
    (s : ∀ j ∈ S, X _⦋n⦌) (hs : Compatible S s) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet) ⟶ X where
  app m := by
    rcases m with ⟨⟨m⟩⟩
    exact TypeCat.ofHom (fun x => descValue S s x)
  naturality := by
    intro m l α
    rcases m with ⟨⟨m⟩⟩
    rcases l with ⟨⟨l⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨j, hjS, hj⟩ := x.property
    let θ : ⦋m⦌ ⟶ ⦋n + 1⦌ := SSet.stdSimplex.objEquiv x.val
    have hθ : ∀ k, θ.toOrderHom k ≠ j := hj
    have hx : x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell S θ j hjS hθ := Subtype.ext (Equiv.symm_apply_apply _ _).symm
    change descValue S s ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet).map α x) = X.map α (descValue S s x)
    rw [hx]
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.map_cell S θ j hjS hθ α.unop
    simp only [Quiver.Hom.op_unop] at hm
    rw [hm, descValue_cell S s hs, descValue_cell S s hs, factor_δ_comp θ j hθ]
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp, CategoryTheory.comp_apply]

/-- 概要：面自身を同じ面で分解した順序写像は恒等。
方針：面の埋め込みの単射性と分解の公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：貼り合わせの元の面への制限。 -/
lemma factor_δ_self {n : ℕ} (j : Fin (n + 2)) :
    SimplexCategory.factor_δ (SimplexCategory.δ j) j = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  apply j.succAboveOrderEmb.injective
  exact congrArg (fun f => f.toOrderHom i)
    (SimplexCategory.factor_δ_spec (SimplexCategory.δ j) j (Fin.succAbove_ne j))

/-- 概要：貼り合わせた写像の各選んだ面の値は元の指定した単体。
方針：その面で評価し、同じ面による分解が恒等であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：slice 境界の各面での一致の検証。 -/
lemma desc_face {n : ℕ} {X : SSet.{u}} (S : Finset (Fin (n + 2)))
    (s : ∀ j ∈ S, X _⦋n⦌) (hs : Compatible S s) (j : Fin (n + 2)) (hjS : j ∈ S) :
    (desc S s hs).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS) = s j hjS := by
  change descValue S s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell S (SimplexCategory.δ j) j hjS _) = _
  rw [descValue_cell S s hs, factor_δ_self]
  rw [op_id]
  exact congrArg (fun f => f (s j hjS)) (X.map_id (op ⦋n⦌))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
