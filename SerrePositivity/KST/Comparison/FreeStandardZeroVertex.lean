module

public import SerrePositivity.KST.Comparison.FreeStandardPrependFaces

/-!
# 自由な退化の標準単体の収縮先の頂点

概要：零点追加の第零次数のもう一つの面は、一定の零点となる。
方針：零次元の標準形の全射を恒等射と同定し、追加した最初の頂点を評価する。
規約：Segal 1974 Proposition 1.6 の標準単体の余分な退化の augmentation 条件。
使われ方：零点への収縮の余分な退化の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped _root_.Simplicial

/--
概要：自由な退化の標準単体の零頂点の標準形。
方針：恒等全射と標準単体の零頂点を組み合わせる。
規約：中間次数と単体次数はともに零。
使われ方：標準単体の収縮先の指定。
-/
def freeStandardZeroNormalForm (n : ℕ) :
    FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋0⦌) where
  degree := ⦋0⦌
  epi := 𝟙 _
  epi_property := inferInstance
  simplex := SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)

/--
概要：自由な退化の標準単体の零頂点。
方針：零点の標準形を実際の模型へ戻す。
規約：元の標準単体の零頂点を持ち上げる。
使われ方：augmentation の切断。
-/
def freeStandardZeroVertex (n : ℕ) : (freeDegeneracies.obj (Δ[n] : SSet.{u})).obj (op ⦋0⦌) :=
  fatNormalFormRealize _ _ (freeStandardZeroNormalForm n)

/--
概要：零次元の元へ零点を追加して最後の面を取ると指定した零頂点になる。
方針：零次元の全射の終域も零であることから、恒等全射の標準形で直接計算する。
規約：この次数の面の番号は一。
使われ方：余分な退化の augmentation に関する恒等式。
-/
theorem freeStandardPrependNormalForm_δ_one {n : ℕ}
    (p : FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋0⦌)) :
    freeDegeneraciesNormalForm (Δ[n] : SSet.{u}) (op ⦋0⦌)
      ((freeDegeneracies.obj (Δ[n] : SSet.{u})).map (SimplexCategory.δ 1).op
        (fatNormalFormRealize _ _ (freeStandardPrependNormalForm p))) =
      freeStandardZeroNormalForm n := by
  rcases p with ⟨k, e, he, x⟩
  let : Epi e := he
  have hk : k = ⦋0⦌ := SimplexCategory.ext (Nat.eq_zero_of_le_zero
    (SimplexCategory.len_le_of_epi e))
  subst k
  have heq : e = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  subst e
  rw [freeDegeneraciesNormalForm_action]
  change fatNormalize (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋0⦌)
    (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv x)))
    (SimplexCategory.δ 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (𝟙 ⦋0⦌)) = freeStandardZeroNormalForm n
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_id, Category.comp_id]
  rw [fatNormalize_eq_of_factorization _ _ _ _ (𝟙 ⦋0⦌) (SimplexCategory.δ 1)
    (Category.id_comp _)]
  change (⟨⦋0⦌, 𝟙 _, _, (Δ[n] : SSet.{u}).map (SimplexCategory.δ 1).op
    (SSet.stdSimplex.objEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv x)))⟩ :
    FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋0⦌)) =
    ⟨⦋0⦌, 𝟙 _, _, SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)⟩
  congr 1
  rw [SSet.stdSimplex.map_objEquiv_symm]
  congr 1
  ext i : 3
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

end SerrePositivity.KST.Comparison
