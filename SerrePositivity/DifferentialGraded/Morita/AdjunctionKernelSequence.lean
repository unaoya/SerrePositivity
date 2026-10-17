module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionKernelSuccessor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # 任意kernelの右随伴を構成する可算近似列

## 概要
生成元被覆から始めて、生成元の全関係を各後続段階で消す可算列を構成する。

## 方針
実際のkernel作用に対する初期射と後続操作を反復し、標的射の互換性を自然なcoconeへまとめる。

## 規約と注意
kernelの列の射影性・局所Hom K-flat性を仮定しない。telescopeでの表現可能性は後続で証明する。

## 使われ方
U16aの一般右随伴の表現対象を、可算telescopeとcompact生成から構成する際の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E)

/-- kernel作用の像からYへの射を持つ一つの近似対象。 -/
structure KernelBrownApproximation where
  obj : DerivedModuleCategory A D
  target : (kernelDerivedTensor A D E K).obj obj ⟶ Y

/-- 近似の生成元の関係を全て消す後続対象。 -/
def kernelBrownApproximationNext (S : KernelBrownApproximation A D E K Y) :
    KernelBrownApproximation A D E K Y :=
  let T := kernelBrownSuccessor A D E K S.target
  ⟨T.obj, T.target⟩

/-- 生成元被覆から始まり、後続操作を反復する可算近似。 -/
def kernelBrownApproximation : ℕ → KernelBrownApproximation A D E K Y
  | 0 => ⟨brownSeed A D E (kernelDerivedTensor A D E K) Y, kernelBrownSeedMap A D E K Y⟩
  | n + 1 => kernelBrownApproximationNext A D E K Y (kernelBrownApproximation n)

/-- 隣り合う近似を結ぶ実際の後続射。 -/
def kernelBrownTransition (n : ℕ) :
    (kernelBrownApproximation A D E K Y n).obj ⟶
      (kernelBrownApproximation A D E K Y (n + 1)).obj :=
  (kernelBrownSuccessor A D E K (kernelBrownApproximation A D E K Y n).target).map

/-- 後続射はYへの標的射を保つ。 -/
lemma kernelBrownTransition_fac (n : ℕ) :
    (kernelDerivedTensor A D E K).map (kernelBrownTransition A D E K Y n) ≫
        (kernelBrownApproximation A D E K Y (n + 1)).target =
      (kernelBrownApproximation A D E K Y n).target :=
  kernelBrownSuccessor_fac A D E K (kernelBrownApproximation A D E K Y n).target

/-- 各段階の生成元からのkernelは、直後の段階で零になる。 -/
lemma kernelBrownTransition_kills (n : ℕ) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj)
    (hf : (kernelDerivedTensor A D E K).map f ≫
      (kernelBrownApproximation A D E K Y n).target = 0) :
    f ≫ kernelBrownTransition A D E K Y n = 0 :=
  kernelBrownSuccessor_kills A D E K (kernelBrownApproximation A D E K Y n).target p f hf

/-- 生成元のkernel像からYへの全射は、どの近似段階でも表せる。 -/
lemma kernelBrownApproximation_generator_surjective (n : ℕ) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj,
      (kernelDerivedTensor A D E K).map g ≫
        (kernelBrownApproximation A D E K Y n).target = f := by
  induction n with
  | zero => exact kernelBrownSeedMap_generator_surjective A D E K Y p f
  | succ n ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g ≫ kernelBrownTransition A D E K Y n, ?_⟩
      rw [Functor.map_comp, Category.assoc, kernelBrownTransition_fac, hg]

/-- 可算近似と後続射をℕ上の実際の図式へまとめる。 -/
def kernelBrownDiagram : ℕ ⥤ DerivedModuleCategory A D :=
  Functor.ofSequence (kernelBrownTransition A D E K Y)

/-- 可算近似のkernel作用の像からYへの互換なcocone。 -/
def kernelBrownTargetCocone :
    Cocone (kernelBrownDiagram A D E K Y ⋙ kernelDerivedTensor A D E K) where
  pt := Y
  ι := NatTrans.ofSequence (fun n => (kernelBrownApproximation A D E K Y n).target) (by
    intro n
    simp only [kernelBrownDiagram, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    erw [Category.comp_id]
    exact kernelBrownTransition_fac A D E K Y n)

/-- 可算図式の標的coconeの成分は各段階の標的射そのもの。 -/
lemma kernelBrownTargetCocone_ι (n : ℕ) :
    (kernelBrownTargetCocone A D E K Y).ι.app n =
      (kernelBrownApproximation A D E K Y n).target := rfl

end SerrePositivity.DifferentialGraded.Morita
