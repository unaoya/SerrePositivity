module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationCofinality
public import SerrePositivity.InfinityCategories.Sheaves.SieveSectionsCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftCofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer

/-!
概要：二段分解の局所 comma 上の指定錐を、元の引き戻し篩の制限錐へ接続する。
方針：三角形の合成の全脚を回収し、実際の cofinal 形状比較で極限性を移す。
  文献対応：HTT 6.2.2.6 の生成系からの降下。係数に極限の存在を追加仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 引き戻し篩から固定 fiber を通り、局所 comma へ入れる全関手。 -/
def pullbackSieveToLocalComma (R S : Sieve U) (t : sieveCategory R) :
    sieveCategory (S.pullback t.obj.hom) ⥤ sieveFactorizationLocalComma R S t :=
  pullbackSieveToFactorizationFiber R S t ⋙ sieveFactorizationLocalInclusion R S t

/-- 局所 comma 上で、分解の最初の始域を取る反変図式。 -/
def sieveFactorizationLocalDiagram (R S : Sieve U) (t : sieveCategory R) :
    (sieveFactorizationLocalComma R S t)ᵒᵖ ⥤ Cᵒᵖ :=
  (CostructuredArrow.proj (sieveFactorizationOuter R S) t).op ⋙ sieveFactorizationDiagram R S

/-- 頂点は t の始域で、脚は局所 comma の二つの三角形の合成。 -/
def sieveFactorizationLocalCone (R S : Sieve U) (t : sieveCategory R) :
    Cone (sieveFactorizationLocalDiagram R S t) where
  pt := Opposite.op t.obj.left
  π :=
    { app := fun B => (B.unop.left.hom.left ≫ B.unop.hom.hom.left).op
      naturality X Y f := by
        change 𝟙 _ ≫ (Y.unop.left.hom.left ≫ Y.unop.hom.hom.left).op =
          (X.unop.left.hom.left ≫ X.unop.hom.hom.left).op ≫ f.unop.left.left.hom.left.op
        rw [Category.id_comp, ← CategoryTheory.op_comp]
        have hw := congrArg (fun z => z.left)
          (CostructuredArrow.w ((sieveFactorizationLocalPush R S t).map f.unop))
        change f.unop.left.left.hom.left ≫ (X.unop.left.hom.left ≫ X.unop.hom.hom.left) =
          Y.unop.left.hom.left ≫ Y.unop.hom.hom.left at hw
        exact congrArg Quiver.Hom.op hw.symm }

/-- 引き戻し篩へ制限すると、元の通常の指定錐を全脚ごと回収する。 -/
lemma sieveFactorizationLocalCone_restrict (R S : Sieve U) (t : sieveCategory R) :
    (sieveFactorizationLocalCone R S t).whisker (pullbackSieveToLocalComma R S t).op =
      sieveCone (S.pullback t.obj.hom) := by
  dsimp only [Cone.whisker, sieveFactorizationLocalCone, sieveCone]
  congr 1
  apply NatTrans.ext
  funext A
  change (A.unop.obj.hom ≫ 𝟙 _).op = A.unop.obj.hom.op
  rw [Category.comp_id]

/-- 元の引き戻し篩から局所 comma への反変な全形状比較は left cofinal。 -/
lemma pullbackSieveToLocalComma_op_isLeftCofinal (R S : Sieve U) (t : sieveCategory R) :
    IsLeftCofinal (nerveMap (pullbackSieveToLocalComma R S t).op) := by
  let e := pullbackSieveFactorizationFiberEquivalence R S t
  have h : (sieveFactorizationLocalPush R S t ⋙ e.inverse) ⊣
      pullbackSieveToLocalComma R S t :=
    (sieveFactorizationLocalAdjunction R S t).comp e.symm.toAdjunction
  exact nerveMap_isLeftCofinal_of_adjunction h.op

variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の係数前層で局所 comma の指定錐を送った錐。 -/
def sieveFactorizationLocalRestrictionCone (R S : Sieve U) (t : sieveCategory R)
    (F : Presheaf C E) : JoinCone
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveFactorizationLocalDiagram R S t)) ≫ F) :=
  ((nerveCone (sieveFactorizationLocalCone R S t)).ulift).postcomp F

/-- 元の係数前層へ送った全錐も、引き戻し篩の元の制限錐と厳密に一致する。 -/
lemma sieveFactorizationLocalRestrictionCone_restrict_val (R S : Sieve U)
    (t : sieveCategory R) (F : Presheaf C E) :
    (restrictJoinCone (sieveFactorizationLocalRestrictionCone R S t F)
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pullbackSieveToLocalComma R S t).op))).val =
        (restrictionCone F (S.pullback t.obj.hom)).val := by
  unfold sieveFactorizationLocalRestrictionCone
  rw [uliftNerveCone_whisker_val, sieveFactorizationLocalCone_restrict]
  rfl

/-- 各引き戻し篩での元の降下条件は、局所 comma 上の同じ指定錐の極限条件と同値。 -/
lemma sieveFactorizationLocalRestrictionCone_isLimit_iff (R S : Sieve U)
    (t : sieveCategory R) (F : Presheaf C E) :
    IsLimitCone (sieveFactorizationLocalRestrictionCone R S t F) ↔
      IsLimitCone (restrictionCone F (S.pullback t.obj.hom)) := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pullbackSieveToLocalComma R S t).op)
  have hj : IsLeftCofinal j :=
    isLeftCofinal_ulift _ (pullbackSieveToLocalComma_op_isLeftCofinal R S t)
  exact (isLimitCone_iff_restrict_of_leftCofinal j hj _ _).trans
    (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _
      (sieveFactorizationLocalRestrictionCone_restrict_val R S t F))

end SerrePositivity.InfinityCategories.Sheaves
