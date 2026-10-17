module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionUncurry
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 両端のdg関手に沿う直接制限と全Hom作用

## 概要
両端のdg関手に沿う直接制限と全Hom作用。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 左作用、次に右作用を制限する直接の両端制限。 -/
def BimoduleCategory.pairedRestrictionFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A D E :=
  BimoduleCategory.middleLeftRestrictionFunctor A B C E G ⋙
    BimoduleCategory.middleRightRestrictionFunctor A B D E F

lemma Bimodule.pairedRestriction_uncurryHom (P : Bimodule A B C)
    (x y : DGTensorCategory A Dᵒᵖ E) :
    (Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P)).uncurryHom x y =
      (F.op.map x.1 y.1 ⊗ₘ G.map x.2 y.2) ≫
        P.uncurryHom (F.op.obj x.1, G.obj x.2) (F.op.obj y.1, G.obj y.2) := by
  rw [Bimodule.rightRestriction_uncurryHom, Bimodule.leftRestriction_uncurryHom,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

lemma BimoduleCategory.pairedRestrictionFunctor_map_value
    {P Q : BimoduleCategory A B C} (q : P ⟶ Q) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).map q) =
      (BimoduleCategory.valueEvaluation A B C (F.obj d) (G.obj e)).map q :=
  (BimoduleCategory.middleRightRestrictionMap_value_eval A B D E F
    ((BimoduleCategory.middleLeftRestrictionFunctor A B C E G).map q) d e).trans
      (BimoduleCategory.middleLeftRestrictionMap_value_eval A B C E G q (F.obj d) e)

lemma Bimodule.pairedRestriction_interchange (P : Bimodule A B C) :
    Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P) =
      Bimodule.leftRestriction A D C E G (Bimodule.rightRestriction A B D C F P) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := Bimodule.rightRestriction A B D E F (Bimodule.leftRestriction A B C E G P))
    (G := Bimodule.leftRestriction A D C E G (Bimodule.rightRestriction A B D C F P))
    (fun _ => rfl)
  intro e e'
  simp only [eqToHom_refl, Category.comp_id]
  change (G.map e e' ≫ P.map (G.obj e) (G.obj e')) ≫
      moduleRestrictionHom A D B F.op _ _ =
    G.map e e' ≫ (P.map (G.obj e) (G.obj e') ≫ moduleRestrictionHom A D B F.op _ _)
  exact Category.assoc _ _ _

/-- 直接左右制限の順序を交換する、右加群ごとに恒等の比較。 -/
def BimoduleCategory.pairedRestrictionInterchangeObjIso (P : BimoduleCategory A B C) :
    (BimoduleCategory.pairedRestrictionFunctor A B C D E F G).obj P ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A D C E G).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P) :=
  eqToIso (Bimodule.pairedRestriction_interchange A B C D E F G _)

@[simp]
lemma BimoduleCategory.pairedRestrictionInterchangeObjIso_hom_eval
    (P : BimoduleCategory A B C) (e : E) :
    (BimoduleCategory.evaluation A D E e).map
        (BimoduleCategory.pairedRestrictionInterchangeObjIso A B C D E F G P).hom = 𝟙 _ := by
  simp only [BimoduleCategory.pairedRestrictionInterchangeObjIso, eqToIso.hom, eqToHom_map]
  rfl

/-- 直接左右制限の交換は任意の閉零bimodule射に自然。 -/
def BimoduleCategory.pairedRestrictionInterchangeIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ≅
      BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A D C E G :=
  NatIso.ofComponents (BimoduleCategory.pairedRestrictionInterchangeObjIso A B C D E F G) (by
    intro P Q q
    apply BimoduleCategory.hom_ext
    intro e
    simp only [CategoryTheory.Functor.map_comp,
      BimoduleCategory.pairedRestrictionInterchangeObjIso_hom_eval, Functor.comp_map]
    change (moduleRestriction A D B F.op).map (q.val (G.obj e)) ≫ 𝟙 _ =
      𝟙 _ ≫ (moduleRestriction A D B F.op).map (q.val (G.obj e))
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded
