module
public import SerrePositivity.DifferentialGraded.Tensor.RestrictBalanced
public import SerrePositivity.DifferentialGraded.Tensor.Maps
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # dg関手に沿うbalanced tensorの比較chain map

## 概要
制限した二因子のtensorから元のtensorへの写像を普遍性で構成する。
準同型性はここでは仮定・主張せず、導来合成比較に使う実際の写像を固定する。

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
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 両作用を制限したtensorから元のtensorへの比較chain map。 -/
def restrictionComparison (M : RightModule A E) (N : LeftModule A E) :
    obj A D (restrictModule A D E F.op M) (F.comp N) ⟶ obj A E M N :=
  desc A D _ _ (restrictFamily A D E F M N
    (homEquiv A E M N _ (𝟙 (obj A E M N))))

@[reassoc (attr := simp)]
lemma ι_restrictionComparison (M : RightModule A E) (N : LeftModule A E) (x : D) :
    ι A D (restrictModule A D E F.op M) (F.comp N) x ≫
        restrictionComparison A D E F M N = ι A E M N (F.obj x) := by
  rw [restrictionComparison, ι_desc]
  exact Category.comp_id _

/-- 比較chain mapは各純粋斉次tensorを同じ元の像へ送る。追加の符号は生じない。 -/
lemma restrictionComparison_element (M : RightModule A E) (N : LeftModule A E) (x : D)
    {r s n : ℤ} (m : (M.obj (op (F.obj x))).X r) (t : (N.obj (F.obj x)).X s)
    (hn : r + s = n) :
    (restrictionComparison A D E F M N).f n
        (element A D (restrictModule A D E F.op M) (F.comp N) x m t hn) =
      element A E M N (F.obj x) m t hn :=
  congrArg (fun k => k.f n
    (ιTensorObj (M.obj (op (F.obj x))) (N.obj (F.obj x)) r s n hn (m ⊗ₜ[A] t)))
      (ι_restrictionComparison A D E F M N x)

/-- 任意のbalanced族への比較は、族の引き戻しと一致する。 -/
lemma restrictionComparison_desc (M : RightModule A E) (N : LeftModule A E)
    {T : Complex A} (a : BalancedFamily A E M N T) :
    restrictionComparison A D E F M N ≫ desc A E M N a =
      desc A D _ _ (restrictFamily A D E F M N a) := by
  apply hom_ext
  intro x
  rw [ι_restrictionComparison_assoc, ι_desc, ι_desc]
  rfl

omit [Small.{u} D] [Small.{u} E] in
lemma rightAction_restrict_family {M M' : RightModule A E}
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x))
    (hf : ∀ x y, rightAction A E M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A E M' x y) (x y : D) :
    rightAction A D (restrictModule A D E F.op M) x y ≫ f (F.obj x) =
      (f (F.obj y) ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫
        rightAction A D (restrictModule A D E F.op M') x y := by
  rw [rightAction_restrict, rightAction_restrict, Category.assoc, hf]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

omit [Small.{u} D] [Small.{u} E] in
lemma leftAction_restrict_family {N N' : LeftModule A E}
    (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hg : ∀ x y, leftAction A E N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A E N' x y) (x y : D) :
    leftAction A D (F.comp N) x y ≫ g (F.obj y) =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g (F.obj x)) ≫ leftAction A D (F.comp N') x y := by
  rw [leftAction_restrict, leftAction_restrict, Category.assoc, hg]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- 比較chain mapは作用と可換な任意の二つのchain map族に関して自然。 -/
lemma restrictionComparison_naturality {M M' : RightModule A E} {N N' : LeftModule A E}
    (f : ∀ x, M.obj (op x) ⟶ M'.obj (op x)) (g : ∀ x, N.obj x ⟶ N'.obj x)
    (hf : ∀ x y, rightAction A E M x y ≫ f x =
      (f y ⊗ₘ 𝟙 (x ⟶[Complex A] y)) ≫ rightAction A E M' x y)
    (hg : ∀ x y, leftAction A E N x y ≫ g y =
      (𝟙 (x ⟶[Complex A] y) ⊗ₘ g x) ≫ leftAction A E N' x y) :
    mapOfFamilies A D (fun x => f (F.obj x)) (fun x => g (F.obj x))
        (rightAction_restrict_family A D E F f hf) (leftAction_restrict_family A D E F g hg) ≫
      restrictionComparison A D E F M' N' =
    restrictionComparison A D E F M N ≫ mapOfFamilies A E f g hf hg := by
  apply hom_ext
  intro x
  simp only [ι_mapOfFamilies_assoc, ι_restrictionComparison,
    ι_restrictionComparison_assoc, ι_mapOfFamilies]

end SerrePositivity.DifferentialGraded.BalancedTensor
