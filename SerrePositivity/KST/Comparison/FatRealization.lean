module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplicialSum
public import SerrePositivity.KST.Comparison.DiagonalRowEvaluation
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# 面だけを同一視した fat realization

概要：各行と標準単体の積の余積を、単射の単体作用だけで同一視する。
方針：関係式の始域と二射を明示し、実際の余等化子を取る。
規約：Segal 1974 Proposition 1.6 と Appendix A の fat realization の単体集合での模型。
使われ方：有限骨格の付着と、対角模型への具体的な比較写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
open SerrePositivity.BisimplicialModel

/--
概要：fat realization の関係式を添字付けする単射。
方針：始点・終点の次元、単体圏の射、単射性を記録する。
規約：恒等射も含め、退化射は含めない。
使われ方：面の関係式の余積。
-/
structure SimplexFace where
  source : ℕ
  target : ℕ
  hom : ⦋source⦌ ⟶ ⦋target⦌
  injective : Function.Injective hom

/--
概要：fat realization の各行の単体の余積。
方針：行と標準単体の積を次数で余積にする。
規約：退化した行の単体も初めは保持する。
使われ方：余等化子の終域。
-/
def fatRowObject (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum (fun n : ℕ => F.obj (op ⦋n⦌) ⊗ Δ[n])

/--
概要：fat realization の面の関係式の余積。
方針：単射の終点の行と、始点の標準単体の積を取る。
規約：全ての単射を添字にする。
使われ方：余等化子の二射の始域。
-/
def fatRelationObject (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum (fun θ : SimplexFace => F.obj (op ⦋θ.target⦌) ⊗ Δ[θ.source])

/--
概要：面の関係式を行の単体作用へ送る射。
方針：単射を外側の関手へ反変に適用する。
規約：小さい次元の行へ入る。
使われ方：fat realization の第一の関係射。
-/
def fatRelationLeft (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    fatRelationObject F ⟶ fatRowObject F :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc (fun θ => (F.map θ.hom.op ▷ Δ[θ.source]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.source)

/--
概要：面の関係式を標準単体の面写像へ送る射。
方針：単射を標準単体の関手へ適用する。
規約：大きい次元の行へ入る。
使われ方：fat realization の第二の関係射。
-/
def fatRelationRight (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    fatRelationObject F ⟶ fatRowObject F :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc (fun θ => (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.target)

/--
概要：二重単体集合の fat realization の実対象。
方針：面の二射の実際の余等化子を取る。
規約：対角模型との局所化可逆性はこの定義の一部ではない。
使われ方：Segal Proposition 1.6 の骨格の模型。
-/
def fatRealization (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  coequalizer (fatRelationLeft F) (fatRelationRight F)

/--
概要：各行と標準単体の積から fat realization への包含。
方針：行の余積の包含に余等化子の射を合成する。
規約：一般にはこの写像の単射性を主張しない。
使われ方：有限骨格の付着と普遍性。
-/
def fatRealizationInclusion (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    F.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ fatRealization F :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) n ≫ coequalizer.π _ _

/--
概要：各行の包含は単射の面の関係式を満たす。
方針：余等化子の条件を関係式の一成分へ制限する。
規約：面の添字には恒等射も含める。
使われ方：fat realization からの射の構成。
-/
theorem fatRealizationInclusion_face (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (θ : SimplexFace) :
    (F.map θ.hom.op ▷ Δ[θ.source]) ≫ fatRealizationInclusion F θ.source =
      (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫
        fatRealizationInclusion F θ.target := by
  have h := congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion
    (fun θ : SimplexFace => F.obj (op ⦋θ.target⦌) ⊗ Δ[θ.source]) θ ≫ t)
      (coequalizer.condition (fatRelationLeft F) (fatRelationRight F))
  have hL : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion
      (fun θ : SimplexFace => F.obj (op ⦋θ.target⦌) ⊗ Δ[θ.source]) θ ≫ fatRelationLeft F =
        (F.map θ.hom.op ▷ Δ[θ.source]) ≫
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.source := rfl
  have hR : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion
      (fun θ : SimplexFace => F.obj (op ⦋θ.target⦌) ⊗ Δ[θ.source]) θ ≫ fatRelationRight F =
        (F.obj (op ⦋θ.target⦌) ◁ SSet.stdSimplex.map θ.hom) ≫
          _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion (fun n => F.obj (op ⦋n⦌) ⊗ Δ[n]) θ.target := rfl
  rw [← Category.assoc, ← Category.assoc, hL, hR] at h
  exact h

end SerrePositivity.KST.Comparison
