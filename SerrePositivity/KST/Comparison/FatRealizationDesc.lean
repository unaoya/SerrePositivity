module

public import SerrePositivity.KST.Comparison.FatRealization

/-!
# fat realization の普遍性と対角への比較

概要：面の関係式を満たす射の族を fat realization からの一意な射へまとめる。
方針：実際の余等化子と添字付き余積の普遍性を順に使う。
規約：Segal 1974 Proposition 1.6、Appendix A。比較の局所化可逆性は別の証明項目。
使われ方：各有限骨格から構成する写像と、対角への具体的な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped _root_.Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：面の関係式を満たす族から fat realization からの射を作る。
方針：余積からの desc を関係式の各成分で可換とし、余等化子へ降ろす。
規約：単射である面の関係式だけを要求する。
使われ方：fat realization の普遍性の存在。
-/
def fatRealizationDesc (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) {Z : SSet.{u}}
    (ι : ∀ n : ℕ, F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ Z)
    (hι : ∀ θ : SimplexFace,
      (F.map θ.hom.op ▷ Δ[θ.source]) ≫ ι θ.source =
        (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫ ι θ.target) :
    fatRealization F ⟶ Z :=
  coequalizer.desc (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc ι) (by
    apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
    intro θ
    change ((F.map θ.hom.op ▷ Δ[θ.source]) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.source) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc ι =
      ((F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.target) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc ι
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc]
    exact hι θ)

/--
概要：fat realization からの desc の各行への制限は元の射である。
方針：余等化子と余積の計算則を適用する。
規約：余等化子の選択の実装に依存しない計算。
使われ方：fat realization の射の自然性と合成の計算。
-/
@[reassoc] theorem fatRealizationInclusion_desc (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {Z : SSet.{u}} (ι : ∀ n : ℕ, F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ Z)
    (hι : ∀ θ : SimplexFace,
      (F.map θ.hom.op ▷ Δ[θ.source]) ≫ ι θ.source =
        (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫ ι θ.target) (n : ℕ) :
    fatRealizationInclusion F n ≫ fatRealizationDesc F ι hι = ι n := by
  rw [fatRealizationInclusion, Category.assoc, fatRealizationDesc, coequalizer.π_desc,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_desc]

/--
概要：fat realization からの二射は各行で一致すれば等しい。
方針：余等化子の全射性と余積の各成分での一意性を使う。
規約：行の包含が単射であることは使わない。
使われ方：関手の恒等・合成と各種の比較の一意性。
-/
theorem fatRealization_hom_ext (F : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    {Z : SSet.{u}} {f g : fatRealization F ⟶ Z}
    (h : ∀ n, fatRealizationInclusion F n ≫ f = fatRealizationInclusion F n ≫ g) : f = g := by
  apply coequalizer.hom_ext
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
  intro n
  exact h n

/--
概要：fat realization から対角単体集合への実際の比較写像。
方針：各行の対角への評価が単射の面の関係式を満たすことを使う。
規約：この定義は比較の局所化可逆性を仮定も主張もしない。
使われ方：Segal の骨格の模型と既存の bar の対角模型の接続。
-/
def fatRealizationToDiagonal (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    fatRealization F ⟶ diagonal.obj F :=
  fatRealizationDesc F (diagonalRowEvaluation F)
    (fun θ => diagonalRowEvaluation_dinaturality F θ.hom)

/--
概要：fat realization の対角への比較は、各行で標準の評価に一致する。
方針：desc の計算則を使う。
規約：全ての次元での等式。
使われ方：比較写像の自然性と骨格への制限。
-/
@[reassoc] theorem fatRealizationInclusion_toDiagonal
    (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    fatRealizationInclusion F n ≫ fatRealizationToDiagonal F = diagonalRowEvaluation F n :=
  fatRealizationInclusion_desc F _ _ n

end SerrePositivity.KST.Comparison
