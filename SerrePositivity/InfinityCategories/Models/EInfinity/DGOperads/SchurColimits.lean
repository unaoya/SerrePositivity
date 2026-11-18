module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Schur
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerColimits
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
模型。文献の定義との比較は後で
# Schur 関手による sifted 余極限の保存

概要：Berger–Moerdijk §1 の自由代数の底の Schur 関手は sifted 余極限を保つ。
方針：各 arity のテンソル冪と固定係数の保存を、図式圏での点ごとの判定へ移す。
規約：直和と coinvariant は既存の有限全単射亜群上の余極限で扱う。
使われ方：自由代数の filtered 余極限と小対象性を検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.SymmetricSequence (Complex A))
  (J : Type u) [SmallCategory J] [IsSifted J]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：Schur 図式の各 arity の評価は sifted 余極限を保つ（BM §1）。
方針：テンソル冪と固定係数によるテンソルの合成と比較する。
規約：零入力の arity も含む。
使われ方：図式圏の点ごとの余極限保存を確認する。 -/
instance schurDiagramEvaluation_preservesSiftedColimits (S : _root_.SerrePositivity.FiniteBijection) :
    PreservesColimitsOfShape J
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagramFunctor A P ⋙ (CategoryTheory.evaluation _ _).obj S) := by
  let e : (powerFunctor S.card ⋙ tensorLeft (P.obj S)) ≅
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagramFunctor A P ⋙ (CategoryTheory.evaluation _ _).obj S) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      change (P.obj S ◁ _root_.SerrePositivity.TensorPowers.map f S.card) ≫ 𝟙 _ =
        𝟙 _ ≫ (𝟙 (P.obj S) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f S.card)
      simp only [Category.comp_id, Category.id_comp, id_tensorHom])
  exact preservesColimitsOfShape_of_natIso e

/-- 概要：Schur 図式の関手は sifted 余極限を保つ（BM §1）。
方針：全ての有限集合で評価した保存から図式圏での保存を得る。
規約：対称群作用を含む図式全体を保つ。
使われ方：coinvariant と直和を取った後の Schur 関手の保存を導く。 -/
instance schurDiagramFunctor_preservesSiftedColimits :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagramFunctor A P) :=
  preservesColimitsOfShape_of_evaluation _ J (fun _ => inferInstance)

/-- 概要：Schur 関手は sifted 余極限を保つ（BM §1）。
方針：図式関手の保存と余極限関手の余極限保存を合成する。
規約：係数環の宇宙内の小さい図式を扱う。
使われ方：自由代数の底の filtered 余極限保存を与える。 -/
instance schurFunctor_preservesSiftedColimits :
    PreservesColimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor
  infer_instance

/-- 概要：Schur 関手は filtered 余極限を保つ（BM §1）。
方針：filtered な形の sifted 性から既存の保存を適用する。
規約：係数環の宇宙内の小さい図式を扱う。
使われ方：自由像の生成射の小対象性を検証する。 -/
instance schurFunctor_preservesFilteredColimits (K : Type u) [SmallCategory K]
    [IsFiltered K] : PreservesColimitsOfShape K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P) := by
  have : IsSifted K := IsFiltered.isSifted
  infer_instance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
