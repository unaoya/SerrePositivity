module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
概要：三角の第三項が十分高い下限を持つとき第一射は指定次数のコホモロジーで同型。
方針：長完全列の隣接する第三項の二つのコホモロジーが零であることを使う。
規約：bounded below 導来圏の標準 t 構造。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の上側切断による固定次数の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Pretriangulated
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/--
概要：第三項が n+1 以上なら三角の第一射は n 次コホモロジーで同型。
方針：長完全列の前後の零対象から単射性と全射性を得る。
規約：三角は元の bounded below 導来圏の distinguished triangle。
使われ方：TT §3、Toën §3.2 の上側切断の像の比較。
-/
lemma plusTriangle_homology_mor₁_isIso (T : Triangle (DerivedCategory.Plus C))
    (hT : T ∈ distTriang _) (n : ℤ) [T.obj₃.IsGE (n + 1)] :
    IsIso ((DerivedCategory.Plus.homologyFunctor C n).map T.mor₁) := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  have hz₀ : IsZero ((H.shift n).obj T.obj₃) :=
    DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ (n + 1) n (by omega)
  have hz₁ : IsZero ((H.shift (n - 1)).obj T.obj₃) :=
    DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ (n + 1) (n - 1) (by omega)
  have : Epi ((H.shift n).map T.mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff T hT n).mpr (hz₀.eq_of_tgt _ _)
  have : Mono ((H.shift n).map T.mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff T hT (n - 1) n (by omega)).mpr
      (hz₁.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((H.shift n).map T.mor₁)

end SerrePositivity.KST.DerivedGeometry
