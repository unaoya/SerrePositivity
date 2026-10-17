module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt

/-! # 中間dg圏への両因子の制限を全Hom自然な閉零射へ拡張する

## 概要
中間dg圏への両因子の制限を全Hom自然な閉零射へ拡張する。

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
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

section Left
variable (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] (F : DGFunctor A D C)

def middleLeftRestrictionMap {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P)) ⟶
      of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P')) :=
  ⟨fun d => f.val (F.obj d), fun d d' => by
    change (F.map d d' ≫ (underlying A B C P).map (F.obj d) (F.obj d')) ≫ _ =
      (F.map d d' ≫ (underlying A B C P').map (F.obj d) (F.obj d')) ≫ _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map d d' ≫ k) (f.property (F.obj d) (F.obj d'))).trans
        (Category.assoc _ _ _).symm)⟩

@[simp]
lemma middleLeftRestrictionMap_value_eval {P P' : BimoduleCategory A B C} (f : P ⟶ P')
    (b : B) (d : D) :
    (valueEvaluation A B D b d).map (middleLeftRestrictionMap A B C D F f) =
      (valueEvaluation A B C b (F.obj d)).map f := rfl

def middleLeftRestrictionFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B D where
  obj P := of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P))
  map f := middleLeftRestrictionMap A B C D F f
  map_id _ := rfl
  map_comp _ _ := rfl

end Left
section Right
variable (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

lemma middleRightRestrictionMap_component {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (d : D) (e : E) :
    moduleMorphismComponent A D
      ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
      ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e)
      ((moduleRestriction A D C F.op).map (g.val e)) d =
        (valueEvaluation A C E (F.obj d) e).map g :=
  moduleRestriction_map_eval A D C F.op (g.val e) d

lemma middleRightRestrictionMap_naturality {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (e e' : E) :
    (Bimodule.rightRestriction A C D E F (underlying A C E Q)).map e e' ≫
      moduleHomPostcompose A D
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e')
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e')
        ((moduleRestriction A D C F.op).map (g.val e')) =
    (Bimodule.rightRestriction A C D E F (underlying A C E Q')).map e e' ≫
      moduleHomPrecompose A D
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e')
        ((moduleRestriction A D C F.op).map (g.val e)) := by
  apply moduleHom_ext
  intro d
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [middleRightRestrictionMap_component]
  have h := valueMap_left_naturality A C E g (F.obj d) e e'
  have hQ := Bimodule.rightRestriction_leftAt_map A C D E F (underlying A C E Q) d e e'
  have hQ' := Bimodule.rightRestriction_leftAt_map A C D E F (underlying A C E Q') d e e'
  rw [← hQ, ← hQ'] at h
  change ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).map e e' ≫
      moduleHomπ A D _ _ d) ≫ _ =
    ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).map e e' ≫
      moduleHomπ A D _ _ d) ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

def middleRightRestrictionMap {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q)) ⟶
      of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q')) :=
  ⟨fun e => (moduleRestriction A D C F.op).map (g.val e),
    middleRightRestrictionMap_naturality A C D E F g⟩

@[simp]
lemma middleRightRestrictionMap_value_eval {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (d : D) (e : E) :
    (valueEvaluation A D E d e).map (middleRightRestrictionMap A C D E F g) =
      (valueEvaluation A C E (F.obj d) e).map g :=
  middleRightRestrictionMap_component A C D E F g d e

def middleRightRestrictionFunctor : BimoduleCategory A C E ⥤ BimoduleCategory A D E where
  obj Q := of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q))
  map g := middleRightRestrictionMap A C D E F g
  map_id Q := by
    apply hom_ext
    intro e
    exact (moduleRestriction A D C F.op).map_id _
  map_comp g h := by
    apply hom_ext
    intro e
    exact (moduleRestriction A D C F.op).map_comp _ _

end Right
end SerrePositivity.DifferentialGraded.BimoduleCategory
