module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestrictionMaps
public import SerrePositivity.DifferentialGraded.Bimodule.ValueIsomorphism
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 合成の外側の左dg作用の制限と相対tensor合成の可換性

## 概要
合成の外側の左dg作用の制限と相対tensor合成の可換性。

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
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E]
  (D : Type t) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側の左作用の制限は相対tensor合成の全Hom作用と可換。 -/
lemma compose_leftRestriction (P : Bimodule A B C) (Q : Bimodule A C E) :
    compose A B C D P (Bimodule.leftRestriction A C E D F Q) =
      Bimodule.leftRestriction A B E D F (compose A B C E P Q) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := compose A B C D P (Bimodule.leftRestriction A C E D F Q))
    (G := Bimodule.leftRestriction A B E D F (compose A B C E P Q)) (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  refine (compose_leftMap_π A B C D P (Bimodule.leftRestriction A C E D F Q) d d' b).trans ?_
  change ((F.map d d' ≫ Q.map (F.obj d) (F.obj d')) ≫
      BalancedTensor.rightHomMap A C (Q.rightAt (F.obj d)) (Q.rightAt (F.obj d'))
        (P.leftAt b)) =
    (F.map d d' ≫ (compose A B C E P Q).map (F.obj d) (F.obj d')) ≫
      moduleHomπ A B _ _ b
  rw [Category.assoc]
  exact congrArg (fun k => F.map d d' ≫ k)
    (compose_leftMap_π A B C E P Q (F.obj d) (F.obj d') b).symm

/-- 合成の外側の左作用の制限を交換する、既存bimodule対象間の同型。 -/
def composeLeftRestrictionIso (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    BimoduleCategory.of A B D
        (compose A B C D (BimoduleCategory.underlying A B C P)
          (Bimodule.leftRestriction A C E D F (BimoduleCategory.underlying A C E Q))) ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
        (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) :=
  eqToIso (compose_leftRestriction A B C E D F _ _)

@[simp]
lemma composeLeftRestrictionIso_hom_value
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
        (composeLeftRestrictionIso A B C E D F P Q).hom = 𝟙 _ := by
  simp only [composeLeftRestrictionIso, eqToIso.hom, eqToHom_map]
  rfl

/-- 外側の制限の比較は、両因子の任意の全Hom自然な閉零射に自然。 -/
lemma composeLeftRestrictionIso_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A B C D f ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeLeftRestrictionIso A B C E D F P' Q').hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E f g) := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeLeftRestrictionIso_hom_value,
    composeMap_value_eval]
  erw [Category.comp_id, Category.id_comp]
  change composeValueMap A B C D f
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) b d =
    (BimoduleCategory.valueEvaluation A B E b (F.obj d)).map (composeMap A B C E f g)
  rw [composeMap_value_eval]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
