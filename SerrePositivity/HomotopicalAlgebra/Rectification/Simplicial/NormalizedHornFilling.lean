module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornOverlap
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.CompatibleHornFillingOperation
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NaturalHornFilling
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedTriangleHorn

/-!
# 中断した任意モデル源への一般化：NormalizedHornFilling

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One horn filling operation preserves all degeneracies in every dimension。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0498][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0498
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One horn filling operation preserves all degeneracies in every dimension

The overlap condition is proved for arbitrary target and parameter.
For a Kan target it yields one simplicial section for each horn, with
strict preservation of every degeneracy at once. The transposed actual
fillers are strictly natural in the original source parameter.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedHornFilling
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))

lemma compatible : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompatibleInputUnion.Compatible
    (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (fun d => DegenerateHornInput.boundary i d K)
    (fun d => DegenerateHornInput.degeneracy d K) := by
  intro j k m x y h
  have he : SSet.yonedaEquiv.symm x ≫ DegenerateHornInput.boundary i j K =
      SSet.yonedaEquiv.symm y ≫ DegenerateHornInput.boundary i k K := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  have hd := DegenerateHornOverlap.eq_of_same_horn K i j k
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) he
  have hf := congrArg SSet.yonedaEquiv hd
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hf

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

abbrev section_ := CompatibleHornFillingOperation.section_ K i hK
  (fun _ : Fin (n + 1) => (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
  (fun d => DegenerateHornInput.boundary i d K)
  (fun d => DegenerateHornInput.degeneracy d K) (compatible K i) (fun _ => rfl)

lemma section_restriction : section_ K i hK ≫ KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  CompatibleHornFillingOperation.section_restriction _ _ _ _ _ _ _ _

lemma section_degeneracy (d : Fin (n + 1)) : DegenerateHornInput.boundary i d K ≫
    section_ K i hK = DegenerateHornInput.degeneracy d K :=
  CompatibleHornFillingOperation.section_prescribed _ _ _ _ _ _ _ _ d

variable {T : SSet.{v}} (b : (SSet.horn (n + 1) i).toSSet ⟶ (ihom T).obj K)

abbrev fill : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K :=
  NaturalHornFilling.fill K i (section_ K i hK) b

lemma fill_restriction : (SSet.horn (n + 1) i).ι ≫ fill K i hK b = b :=
  NaturalHornFilling.fill_restriction K i (section_ K i hK) b (section_restriction K i hK)

lemma fill_reindex {U : SSet.{v}} (j : U ⟶ T) :
    fill K i hK (b ≫ (pre j).app K) = fill K i hK b ≫ (pre j).app K :=
  NaturalHornFilling.fill_reindex K i (section_ K i hK) b j

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    uncurry (fill K i hK (b ≫ (pre j).app K)) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫ uncurry (fill K i hK b) :=
  NaturalHornFilling.family_reindex K i (section_ K i hK) b j

lemma fill_degenerate (d : Fin (n + 1))
    (e : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ (ihom T).obj K) :
    fill K i hK ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d ≫ e) =
      SSet.stdSimplex.σ d ≫ e :=
  NaturalHornFilling.fill_degenerate K i (section_ K i hK) d e (section_degeneracy K i hK d)

def compare (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : (SSet.horn (n + 1) i).ι ≫ a = b) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn (n + 1) i).ι b a (fill K i hK b) :=
  Classical.choice (LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy _
    ParameterizedHornChoices.horn_localized_isIso (SimplexParameterHom.native_kan T K hK)
    b a (fill K i hK b) ha (fill_restriction K i hK b))

lemma triangle_section (k : Fin 3) : section_ K k hK = NormalizedTriangleHorn.section_ K k hK :=
  rfl

end SerrePositivity.SimplicialModel.NormalizedHornFilling
