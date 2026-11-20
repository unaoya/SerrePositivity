module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# 単体圏の像分解と単射との合成

概要：単体圏の epi–mono 分解を、単射との後合成と全射の場合に計算する。
方針：骨格圏であることによる像の対象の等式と、強 epi–mono 分解の一意性を使う。
規約：Segal 1974 Proposition 1.6、Appendix A の fat realization の標準形の補助。
使われ方：面の関係式を全射な標準形へ正規化する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：単体圏の射に単射を後合成しても、像の対象は同じである。
方針：元の像分解の単射に後合成し、epi–mono 分解の一意性を使う。
規約：骨格圏なので同型ではなく対象の等式になる。
使われ方：fat realization の面の関係式の像の比較。
-/
theorem simplexImage_comp_mono {X Y Z : SimplexCategory} (f : X ⟶ Y) (i : Y ⟶ Z) [Mono i] :
    image (f ≫ i) = image f := by
  apply SimplexCategory.image_eq (e := factorThruImage f) (i := image.ι f ≫ i)
  rw [← Category.assoc, image.fac]

/--
概要：単射との後合成の像への射は、元の像への射の対象の輸送である。
方針：像の対象の等式に沿って元の epi–mono 分解を輸送する。
規約：eqToHom の向きを像の始域に合わせる。
使われ方：fat realization の面に沿う行の作用の一致。
-/
theorem simplexImage_comp_mono_ι {X Y Z : SimplexCategory} (f : X ⟶ Y) (i : Y ⟶ Z) [Mono i] :
    image.ι (f ≫ i) = eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono f i) ≫ image.ι f ≫ i := by
  apply SimplexCategory.image_ι_eq
    (e := factorThruImage f ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono f i).symm)
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, image.fac]

/--
概要：単射との後合成の全射因子は、元の全射因子の終域の輸送である。
方針：輸送した epi–mono 分解に全射因子の一意性を適用する。
規約：始域は元の射の始域のまま。
使われ方：面の関係式の全射な添字が一致すること。
-/
theorem simplexFactorThruImage_comp_mono {X Y Z : SimplexCategory}
    (f : X ⟶ Y) (i : Y ⟶ Z) [Mono i] :
    factorThruImage (f ≫ i) =
      factorThruImage f ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono f i).symm := by
  apply SimplexCategory.factorThruImage_eq
    (i := eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_comp_mono f i) ≫ image.ι f ≫ i)
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, image.fac]

/--
概要：全射な単体圏の射の像の対象はその終域である。
方針：恒等の単射を持つ epi–mono 分解を使う。
規約：像の対象の等式の向きは像から終域。
使われ方：全射な標準形の復元。
-/
theorem simplexImage_of_epi {X Y : SimplexCategory} (f : X ⟶ Y) [Epi f] : image f = Y := by
  apply SimplexCategory.image_eq (e := f) (i := 𝟙 Y)
  simp

/--
概要：全射の像の包含は、像と終域の等式の射である。
方針：終域の恒等射の始域を輸送して像分解の一意性を使う。
規約：像の包含の具体的な輸送。
使われ方：全射の正規化で行の作用が恒等となること。
-/
theorem simplexImage_ι_of_epi {X Y : SimplexCategory} (f : X ⟶ Y) [Epi f] :
    image.ι f = eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi f) := by
  apply SimplexCategory.image_ι_eq (e := f ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi f).symm)
  simp

/--
概要：全射の像への因子は、終域を像へ輸送した元の全射である。
方針：輸送した恒等の像分解の一意性を使う。
規約：輸送の射は終域から像へ向く。
使われ方：全射な標準形の添字の復元。
-/
theorem simplexFactorThruImage_of_epi {X Y : SimplexCategory} (f : X ⟶ Y) [Epi f] :
    factorThruImage f = f ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi f).symm := by
  apply SimplexCategory.factorThruImage_eq (i := eqToHom (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexImage_of_epi f))
  simp

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
