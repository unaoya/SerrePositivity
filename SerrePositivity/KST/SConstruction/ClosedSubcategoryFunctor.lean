module
public import SerrePositivity.KST.SConstruction.SClosedStableIso

/-! # 閉じた全部分圏を保つ完全関手の制限
概要：閉じた頂点条件を保つ完全関手を、対応する全部分圏の完全関手に制限する。
方針：全部分複体への持ち上げと包含による完全性の反映を使う。
規約：所属条件は任意の対象について明示する。使われ方：相対加法性の入力関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 所属条件を保つ完全関手の全部分圏への底の制限。 -/
def closedSubcategoryMap {X Y : StableModel.{u}}
    (P : ClosedStablePredicate X) (Q : ClosedStablePredicate Y) (f : X ⟶ Y)
    (hf : ∀ x, P.predicate x → Q.predicate (f.val.app (Opposite.op ⦋0⦌) x)) :
    closedSubcategory P ⟶ closedSubcategory Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift Q.predicate ((closedStableInclusion P).val ≫ f.val)
    (fun x => hf x.val (closedSubcategory_vertex P x))

/-- 制限の包含後の射は元の完全関手との合成。 -/
lemma closedSubcategoryMap_inclusion {X Y : StableModel.{u}}
    (P : ClosedStablePredicate X) (Q : ClosedStablePredicate Y) (f : X ⟶ Y)
    (hf : ∀ x, P.predicate x → Q.predicate (f.val.app (Opposite.op ⦋0⦌) x)) :
    closedSubcategoryMap P Q f hf ≫ (closedStableInclusion Q).val =
      (closedStableInclusion P).val ≫ f.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 所属条件を保つ完全関手は全部分圏の完全関手に制限される。 -/
def closedStableMap {X Y : StableModel.{u}}
    (P : ClosedStablePredicate X) (Q : ClosedStablePredicate Y) (f : X ⟶ Y)
    (hf : ∀ x, P.predicate x → Q.predicate (f.val.app (Opposite.op ⦋0⦌) x)) :
    closedStableModel P ⟶ closedStableModel Q :=
  ⟨closedSubcategoryMap P Q f hf, by
    apply preservesCofiberData_fullSubcomplex_of_comp Q.predicate
    change PreservesCofiberData (closedSubcategoryMap P Q f hf ≫ (closedStableInclusion Q).val)
    rw [closedSubcategoryMap_inclusion]
    exact (closedStableInclusion P).property.comp f.property⟩

/-- 完全な制限は元の関手と包含後に厳密に可換。 -/
lemma closedStableMap_inclusion {X Y : StableModel.{u}}
    (P : ClosedStablePredicate X) (Q : ClosedStablePredicate Y) (f : X ⟶ Y)
    (hf : ∀ x, P.predicate x → Q.predicate (f.val.app (Opposite.op ⦋0⦌) x)) :
    closedStableMap P Q f hf ≫ closedStableInclusion Q = closedStableInclusion P ≫ f :=
  Subtype.ext (closedSubcategoryMap_inclusion P Q f hf)

/-- 恒等関手の全部分圏への制限は恒等関手。 -/
lemma closedStableMap_id {X : StableModel.{u}} (P : ClosedStablePredicate X) :
    closedStableMap P P (𝟙 X) (fun _ hx => hx) = 𝟙 (closedStableModel P) := by
  apply closedStableInclusion_cancel P
  rw [closedStableMap_inclusion, Category.comp_id, Category.id_comp]

/-- 完全関手の制限は合成と厳密に可換。 -/
lemma closedStableMap_comp {X Y Z : StableModel.{u}}
    (P : ClosedStablePredicate X) (Q : ClosedStablePredicate Y) (R : ClosedStablePredicate Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ x, P.predicate x → Q.predicate (f.val.app (Opposite.op ⦋0⦌) x))
    (hg : ∀ y, Q.predicate y → R.predicate (g.val.app (Opposite.op ⦋0⦌) y)) :
    closedStableMap P R (f ≫ g) (fun x hx => hg _ (hf x hx)) =
      closedStableMap P Q f hf ≫ closedStableMap Q R g hg := by
  apply closedStableInclusion_cancel R
  calc
    _ = closedStableInclusion P ≫ (f ≫ g) := closedStableMap_inclusion P R _ _
    _ = (closedStableMap P Q f hf ≫ closedStableInclusion Q) ≫ g :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ g) (closedStableMap_inclusion P Q f hf).symm)
    _ = closedStableMap P Q f hf ≫ (closedStableMap Q R g hg ≫ closedStableInclusion R) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => closedStableMap P Q f hf ≫ t)
          (closedStableMap_inclusion Q R g hg).symm)
    _ = _ := (Category.assoc _ _ _).symm

end SerrePositivity.KST.SConstruction
