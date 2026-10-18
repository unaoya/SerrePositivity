module

public import SerrePositivity.KST.DerivedGeometry.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：右端の全射が関手適用後に分裂するとき、pullback の射影にも分裂を構成する。
方針：保存された pullback の比較同型を使い、元の中央対象からの切断を作る。
規約：分裂は指定された関手への適用後だけでよい。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の各項の injective 因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  (S : ShortComplex C) {E : C} (p : E ⟶ S.X₃)
  (σ : F.obj S.X₃ ⟶ F.obj E) (hσ : σ ≫ F.map p = 𝟙 _)

/--
概要：保存された pullback の第一射影の切断。
方針：元の中央対象の恒等と右端の切断の合成を pullback へ持ち上げる。
規約：関手適用後の射として構成する。
使われ方：Stacks Lemma 19.12.5、TT §3 の injective 部分対象の包含。
-/
def pullbackFactorSection : F.obj S.X₂ ⟶ F.obj (pullback S.g p) :=
  pullback.lift (𝟙 _) (F.map S.g ≫ σ) (by simp [Category.assoc, hσ]) ≫
    inv (pullbackComparison F S.g p)

/--
概要：構成した切断と第一射影の合成は恒等。
方針：pullback の比較射と第一射影の公式を使う。
規約：元の関手で写した射影。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の単射な因子の証明。
-/
lemma pullbackFactorSection_fst :
    pullbackFactorSection F S p σ hσ ≫ F.map (pullback.fst S.g p) = 𝟙 _ := by
  dsimp only [pullbackFactorSection]
  rw [← pullbackComparison_comp_fst F S.g p]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

/--
概要：構成した切断は元の第一射と pullback の第一射の因子化を与える。
方針：比較射で写した二つの射影を照合し、短複体の合成の零性を使う。
規約：第一射の単射性・短完全性自体はこの公式に不要。
使われ方：Stacks Lemma 19.12.5、TT §3・§8 の各成分の injective 因子化。
-/
lemma pullbackFactorSection_factor :
    F.map S.f ≫ pullbackFactorSection F S p σ hσ = F.map (shortComplexPullback S p).f := by
  have hs : pullbackFactorSection F S p σ hσ ≫ pullbackComparison F S.g p =
      pullback.lift (𝟙 _) (F.map S.g ≫ σ) (by simp [Category.assoc, hσ]) := by
    dsimp only [pullbackFactorSection]
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (pullbackComparison F S.g p)).mp
  rw [Category.assoc, hs]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullbackComparison_comp_fst, ← F.map_comp]
    simp [shortComplexPullback]
  · simp only [Category.assoc, pullback.lift_snd, pullbackComparison_comp_snd, ← F.map_comp]
    simp [shortComplexPullback]
    rw [← Category.assoc, ← F.map_comp, S.zero, F.map_zero, zero_comp]

/--
概要：pullback の切断は単射。
方針：第一射影との合成が恒等であることを使う。
規約：写した圏の実際の単射。
使われ方：Stacks Lemma 19.12.5、Toën §3.2 の injective 部分対象。
-/
instance pullbackFactorSection_mono : Mono (pullbackFactorSection F S p σ hσ) :=
  mono_of_mono_fac (pullbackFactorSection_fst F S p σ hσ)

end SerrePositivity.KST.DerivedGeometry
