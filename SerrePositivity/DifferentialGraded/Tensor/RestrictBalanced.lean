module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Module.RestrictionAction
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.CurryingNaturality

/-! # dg関手に沿うbalanced族の引き戻し

## 概要
右作用のKoszul交換を保ち、任意次数の関係を元のdg圏の関係へ送る。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (F : DGFunctor A D E)

lemma rightAction_restrict (M : RightModule A E) (x y : D) :
    rightAction A D (restrictModule A D E F.op M) x y =
      (𝟙 (M.obj (op (F.obj y))) ⊗ₘ F.map x y) ≫ rightAction A E M (F.obj x) (F.obj y) := by
  change (signedSwap (M.obj (op (F.obj y))) (homObject A D x y)).hom ≫
    uncurryRight (F.map x y ≫ M.map (op (F.obj y)) (op (F.obj x))) =
      (𝟙 _ ⊗ₘ F.map x y) ≫
        (signedSwap (M.obj (op (F.obj y))) (homObject A E (F.obj x) (F.obj y))).hom ≫
          uncurryRight (M.map (op (F.obj y)) (op (F.obj x)))
  rw [uncurryRight_precompose]
  change (signedSwap _ _).hom ≫ (F.map x y ⊗ₘ 𝟙 _) ≫ _ = _
  rw [← Category.assoc, ← signedSwap_naturality, Category.assoc]

lemma leftAction_restrict (N : LeftModule A E) (x y : D) :
    leftAction A D (F.comp N) x y =
      (F.map x y ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫ leftAction A E N (F.obj x) (F.obj y) := by
  change uncurryRight (F.map x y ≫ N.map (F.obj x) (F.obj y)) = _
  exact uncurryRight_precompose (F.map x y) (N.map (F.obj x) (F.obj y))

variable [Small.{u} D]

/-- target上のbalanced族を、両作用を制限したsource上のbalanced族へ引き戻す。 -/
def restrictFamily (M : RightModule A E) (N : LeftModule A E) {T : Complex A}
    (a : BalancedFamily A E M N T) :
    BalancedFamily A D (restrictModule A D E F.op M) (F.comp N) T := by
  refine ⟨fun x => a.val (F.obj x), ?_⟩
  intro x y
  rw [rightAction_restrict, comp_whiskerRight, Category.assoc]
  change ((𝟙 (M.obj (op (F.obj y))) ⊗ₘ F.map x y) ▷ N.obj (F.obj x)) ≫
      (rightAction A E M (F.obj x) (F.obj y) ▷ N.obj (F.obj x)) ≫ a.val (F.obj x) =
    (α_ (M.obj (op (F.obj y))) (x ⟶[Complex A] y) (N.obj (F.obj x))).hom ≫
      M.obj (op (F.obj y)) ◁ leftAction A D (F.comp N) x y ≫ a.val (F.obj y)
  rw [a.property, leftAction_restrict, whiskerLeft_comp]
  rw [tensorHom_def, id_whiskerRight, Category.id_comp, associator_naturality_middle_assoc]
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc]

@[reassoc] lemma ι_restrictFamily_desc (M : RightModule A E) (N : LeftModule A E)
    {T : Complex A} (a : BalancedFamily A E M N T) (x : D) :
    ι A D (restrictModule A D E F.op M) (F.comp N) x ≫
      desc A D _ _ (restrictFamily A D E F M N a) = a.val (F.obj x) :=
  ι_desc A D _ _ _ x

end SerrePositivity.DifferentialGraded.BalancedTensor
