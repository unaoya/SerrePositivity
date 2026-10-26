module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelTriangleCoordinates

/-!
概要：元の余核図式の任意の区間値と加法的な合成則。
方針：任意の三端点への制限に元の S₂ の三辺関係を適用する。
規約：区間値は元の端点制限から作り、bar の合成則を仮定しない。
使われ方：元の余核図式から群 nerve への単体的射の構成。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 概要：二つの元の端点を結ぶ標準辺の順序写像。
方針：二端点の列の単調性を検査する。
規約：一致する端点も許す。
使われ方：余核図式の元の区間値。 -/
def cokernelIntervalOrder {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    Fin 2 →o Fin (n + 1) where
  toFun := ![i, j]
  monotone' a b hab := by
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · exact hij
    · simp at hab
    · exact le_rfl

/-- 概要：三つの元の端点を結ぶ二単体の順序写像。
方針：三端点の列の単調性を検査する。
規約：退化した三端点も許す。
使われ方：元の S₂ の三辺関係の任意区間への移送。 -/
def cokernelTripleOrder {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    Fin 3 →o Fin (n + 1) where
  toFun := ![i, j, k]
  monotone' a b hab := by
    fin_cases a <;> fin_cases b
    · exact le_rfl
    · exact hij
    · exact hij.trans hjk
    · simp at hab
    · exact le_rfl
    · exact hjk
    · simp at hab
    · simp at hab
    · exact le_rfl

/-- 概要：同じ端点の区間値は零。
方針：元の端点写像が定値であることを計算する。
規約：元の余核の定値制限の消滅を使う。
使われ方：群 nerve の恒等射。 -/
lemma cutCokernel_interval_self {n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : cutKZeroCokernel n f) (i : Fin (n + 1)) :
    cutCokernelRestriction f (cokernelIntervalOrder i i le_rfl) a = 0 := by
  have he : cokernelIntervalOrder i i le_rfl = OrderHom.const (Fin 2) i := by
    apply DFunLike.ext
    intro b
    fin_cases b <;> rfl
  exact (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) he) a).trans
    (DFunLike.congr_fun (cutCokernelRestriction_constant f i) a)

/-- 概要：任意の三端点の区間値は元の余核上で加法的。
方針：三端点への制限後に元の S₂ の三辺関係を適用する。
規約：元の端点制限の合成則を保つ。
使われ方：障害 bar の群 nerve における射の合成。 -/
lemma cutCokernel_interval_add {n : ℕ} {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : cutKZeroCokernel n f) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    cutCokernelRestriction f (cokernelIntervalOrder i k (hij.trans hjk)) a =
      cutCokernelRestriction f (cokernelIntervalOrder i j hij) a +
      cutCokernelRestriction f (cokernelIntervalOrder j k hjk) a := by
  let φ := cokernelTripleOrder i j k hij hjk
  have em : φ.comp (SimplexCategory.δ (1 : Fin 3)).toOrderHom =
      cokernelIntervalOrder i k (hij.trans hjk) := by
    apply DFunLike.ext
    intro b
    fin_cases b <;> rfl
  have el : φ.comp (SimplexCategory.δ (2 : Fin 3)).toOrderHom =
      cokernelIntervalOrder i j hij := by
    apply DFunLike.ext
    intro b
    fin_cases b <;> rfl
  have er : φ.comp (SimplexCategory.δ (0 : Fin 3)).toOrderHom =
      cokernelIntervalOrder j k hjk := by
    apply DFunLike.ext
    intro b
    fin_cases b <;> rfl
  have hm := (DFunLike.congr_fun (cutCokernelRestriction_comp f
    (SimplexCategory.δ (1 : Fin 3)).toOrderHom φ) a).symm.trans
      (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) em) a)
  have hl := (DFunLike.congr_fun (cutCokernelRestriction_comp f
    (SimplexCategory.δ (2 : Fin 3)).toOrderHom φ) a).symm.trans
      (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) el) a)
  have hr := (DFunLike.congr_fun (cutCokernelRestriction_comp f
    (SimplexCategory.δ (0 : Fin 3)).toOrderHom φ) a).symm.trans
      (DFunLike.congr_fun (congrArg (cutCokernelRestriction f) er) a)
  exact hm.symm.trans ((cutCokernel_triangle f (cutCokernelRestriction f φ a)).trans
    (congrArg₂ (· + ·) hl hr))

end SerrePositivity.KST.SConstruction.Cofinality
