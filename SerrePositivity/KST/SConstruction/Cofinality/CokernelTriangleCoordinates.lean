module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelEdgeCoordinates

/-!
概要：元の S₂ 余核の三辺は bar の加法関係を満たす。
方針：同じ切断 cofiber の恒等分解を長辺で評価する。
規約：三辺の射は元の単体的面写像そのもの。
使われ方：全 S 余核図式から群 nerve への写像の合成則。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：元の切断は余核上でも恒等を左右に分解する。
方針：元の K₀ の切断加法関係を同じ商へ写す。
規約：同じ S_n 上の元の二角の制限を使う。
使われ方：余核の三辺の加法関係。 -/
lemma cutCokernel_cut_decomposition (n : ℕ) (k : Fin (n + 1))
    {X Y : StableModel.{u}} (f : X ⟶ Y) (a : cutKZeroCokernel n f) :
    a = cutCokernelRestriction f (cutCornerOrder k 0 0) a +
      cutCokernelRestriction f (cutCornerOrder k 1 1) a := by
  induction a using Quotient.inductionOn with | h a => ?_
  have h := DFunLike.congr_fun (cutKZero_id n k Y) a
  have hl := DFunLike.congr_fun (cutKZero_corner n k Y 0 0) a
  have hr := DFunLike.congr_fun (cutKZero_corner n k Y 1 1) a
  have ha := h.trans (congrArg₂ (· + ·) hl hr)
  let π := QuotientAddGroup.mk' (triangulatedKZeroSourceMap ((sEndofunctor n).map f)).range
  exact (congrArg π ha).trans (map_add π _ _)

/-- 概要：S₂ の元の三辺の余核類は長辺が短辺の和となる。
方針：同じ切断の二角を長辺で評価すると元の短辺となることを計算する。
規約：元の δ₁・δ₂・δ₀ の端点制限を使う。
使われ方：群 nerve の合成則の検証。 -/
lemma cutCokernel_triangle {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : cutKZeroCokernel 2 f) :
    cutCokernelRestriction f (SimplexCategory.δ (1 : Fin 3)).toOrderHom a =
      cutCokernelRestriction f (SimplexCategory.δ (2 : Fin 3)).toOrderHom a +
      cutCokernelRestriction f (SimplexCategory.δ (0 : Fin 3)).toOrderHom a := by
  let k : Fin 3 := 1
  let θ := (SimplexCategory.δ (1 : Fin 3)).toOrderHom
  have el : (cutCornerOrder k 0 0).comp θ =
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom := by
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  have er : (cutCornerOrder k 1 1).comp θ =
      (SimplexCategory.δ (0 : Fin 3)).toOrderHom := by
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  have hl := (DFunLike.congr_fun (cutCokernelRestriction_comp f θ
    (cutCornerOrder k 0 0)) a).symm.trans
      (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) el) a)
  have hr := (DFunLike.congr_fun (cutCokernelRestriction_comp f θ
    (cutCornerOrder k 1 1)) a).symm.trans
      (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) er) a)
  exact (congrArg (cutCokernelRestriction f θ) (cutCokernel_cut_decomposition 2 k f a)).trans
    ((map_add _ _ _).trans (congrArg₂ (· + ·) hl hr))

end SerrePositivity.KST.SConstruction.Cofinality
