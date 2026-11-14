module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 標準単体の零頂点への実収縮

概要：標準単体を零頂点から恒等写像へ結ぶ単体的ホモトピーを構成する。
方針：単調な区間座標が零の間は零頂点、一区間では元の単体を取る。
規約：Segal 1974 Proposition 1.6 の単体上の作用の比較。位相的実現を経ず単調写像で証明する。
使われ方：単体でパラメータ付けられた作用を頂点での作用と比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped _root_.Simplicial

/--
概要：標準単体と区間の単体から収縮の単体を作る。
方針：区間座標が零の頂点を零へ送り、それ以外を元の単体へ送る。
規約：Segal 1974 Proposition 1.6 の単体上の縮約の組合せ的模型。
使われ方：収縮の全単体次数での構成。
-/
def simplexContractionAt (n : ℕ) {d : SimplexCategoryᵒᵖ}
    (s : (Δ[n] : SSet.{u}).obj d) (t : (Δ[1] : SSet.{u}).obj d) : (Δ[n] : SSet.{u}).obj d :=
  SSet.stdSimplex.objMk
    { toFun := fun i => if (SSet.stdSimplex.objEquiv t).toOrderHom i = 0 then 0
        else (SSet.stdSimplex.objEquiv s).toOrderHom i
      monotone' := by
        intro i j hij
        by_cases hi : (SSet.stdSimplex.objEquiv t).toOrderHom i = 0
        · simp only [hi, ↓reduceIte]
          exact Fin.zero_le _
        · by_cases hj : (SSet.stdSimplex.objEquiv t).toOrderHom j = 0
          · have ht := (SSet.stdSimplex.objEquiv t).toOrderHom.monotone hij
            rw [hj] at ht
            exact False.elim (hi (le_antisymm ht (Fin.zero_le _)))
          · simp only [hi, hj, ↓reduceIte]
            exact (SSet.stdSimplex.objEquiv s).toOrderHom.monotone hij }

/--
概要：標準単体の収縮の区間写像。
方針：単体と区間の頂点での単調な構成を全次数で束ねる。
規約：Segal 1974 Proposition 1.6。単体的作用との可換性は定義による。
使われ方：単体上の作用のホモトピー比較。
-/
def simplexContractionMap (n : ℕ) :
    (Δ[n] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Δ[n] where
  app _ := TypeCat.ofHom (fun p => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt n p.1 p.2)
  naturality _ _ _ := rfl

/--
概要：標準単体の零頂点への定数写像から恒等写像への実単体的ホモトピー。
方針：区間の両端で単調な収縮の式を評価する。
規約：Segal 1974 Proposition 1.6 の局所計算。零頂点を固定する。
使われ方：パラメータ付き平行移動を零頂点の平行移動へ還元する。
-/
noncomputable def simplexContraction (n : ℕ) :
    SSet.Homotopy (SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm 0))
      (𝟙 (Δ[n] : SSet.{u})) where
  h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap n
  h₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (if (0 : Fin 2) = 0 then (0 : Fin (n + 1))
      else (SSet.stdSimplex.objEquiv s).toOrderHom i) = 0
    rfl
  h₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    change (if (1 : Fin 2) = 0 then (0 : Fin (n + 1)) else
      (SSet.stdSimplex.objEquiv s).toOrderHom i) = (SSet.stdSimplex.objEquiv s).toOrderHom i
    rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/--
概要：標準単体上の写像を零頂点の値への定数写像から結ぶ。
方針：標準単体の実収縮に与えられた写像を後合成する。
規約：Segal 1974 Proposition 1.6 の単体上の局所比較。
使われ方：パラメータ付き作用を頂点での作用へ結ぶ。
-/
noncomputable def simplexMapContraction {n : ℕ} {X : SSet.{u}} (f : (Δ[n] : SSet.{u}) ⟶ X) :
    SSet.Homotopy (SSet.const (X := (Δ[n] : SSet.{u}))
      (f.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm 0))) f where
  h := (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction n).h ≫ f
  h₀ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction n).h₀, SSet.const_comp]
    rfl
  h₁ := by
    rw [← Category.assoc, (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction n).h₁, Category.id_comp]
    rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContraction := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionAt := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexMapContraction := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContraction._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContraction._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContraction._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContraction._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContraction._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionAt._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionAt._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionAt._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionAt._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexContractionMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexContractionMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexMapContraction._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexMapContraction._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplexMapContraction._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexMapContraction._proof_3
