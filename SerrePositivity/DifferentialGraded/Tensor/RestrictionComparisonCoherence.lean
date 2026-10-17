module
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison

/-! # 制限tensor比較のdg関手合成に関する整合性

## 概要
制限tensor比較のdg関手合成に関する整合性。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] (T : Type z) [DGCategory A T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

lemma rightAction_restrict_comp (M : RightModule A T) (x y : D) :
    rightAction A D (restrictModule A D E F.op (restrictModule A E T G.op M)) x y =
      rightAction A D (restrictModule A D T (F.comp G).op M) x y := by
  change (signedSwap _ _).hom ≫ uncurryRight
    (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫ M.map _ _)) =
      (signedSwap _ _).hom ≫ uncurryRight
        ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ M.map _ _)
  rw [Category.assoc]

lemma leftAction_restrict_comp (N : LeftModule A T) (x y : D) :
    leftAction A D (F.comp (G.comp N)) x y = leftAction A D ((F.comp G).comp N) x y := by
  change uncurryRight (F.map x y ≫ (G.map (F.obj x) (F.obj y) ≫ N.map _ _)) =
    uncurryRight ((F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ N.map _ _)
  rw [Category.assoc]

variable [Small.{u} D]

/-- 反復制限と合成制限のtensorを恒等成分で比較する。 -/
def restrictionComparisonCompIso (M : RightModule A T) (N : LeftModule A T) :
    obj A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) ≅
      obj A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) where
  hom := mapOfFamilies A D (fun _ => 𝟙 _) (fun _ => 𝟙 _)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        rightAction_restrict_comp A D E T F G M x y)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        leftAction_restrict_comp A D E T F G N x y)
  inv := mapOfFamilies A D (fun _ => 𝟙 _) (fun _ => 𝟙 _)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        (rightAction_restrict_comp A D E T F G M x y).symm)
    (fun x y => by
      simpa only [tensorHom_id, id_whiskerRight, Category.comp_id, Category.id_comp] using
        (leftAction_restrict_comp A D E T F G N x y).symm)
  hom_inv_id := by
    apply hom_ext
    intro x
    simp only [ι_mapOfFamilies_assoc, ι_mapOfFamilies, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply hom_ext
    intro x
    simp only [ι_mapOfFamilies_assoc, ι_mapOfFamilies, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id]

@[reassoc (attr := simp)]
lemma ι_restrictionComparisonCompIso_hom (M : RightModule A T) (N : LeftModule A T) (x : D) :
    ι A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) x ≫
        (restrictionComparisonCompIso A D E T F G M N).hom =
      ι A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) x := by
  dsimp only [restrictionComparisonCompIso]
  simp only [ι_mapOfFamilies, tensorHom_id, id_whiskerRight, Category.id_comp]

@[reassoc (attr := simp)]
lemma ι_restrictionComparisonCompIso_inv (M : RightModule A T) (N : LeftModule A T) (x : D) :
    ι A D (restrictModule A D T (F.comp G).op M) ((F.comp G).comp N) x ≫
        (restrictionComparisonCompIso A D E T F G M N).inv =
      ι A D (restrictModule A D E F.op (restrictModule A E T G.op M)) (F.comp (G.comp N)) x := by
  dsimp only [restrictionComparisonCompIso]
  simp only [ι_mapOfFamilies, tensorHom_id, id_whiskerRight, Category.id_comp]

variable [Small.{u} E] [Small.{u} T]

/-- 二段階での比較chain mapは合成関手による一段階の比較と可換。 -/
lemma restrictionComparison_comp (M : RightModule A T) (N : LeftModule A T) :
    (restrictionComparisonCompIso A D E T F G M N).hom ≫
        restrictionComparison A D T (F.comp G) M N =
      restrictionComparison A D E F (restrictModule A E T G.op M) (G.comp N) ≫
        restrictionComparison A E T G M N := by
  apply hom_ext
  intro x
  rw [ι_restrictionComparisonCompIso_hom_assoc, ι_restrictionComparison,
    ι_restrictionComparison_assoc, ι_restrictionComparison]
  rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
