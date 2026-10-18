module
public import SerrePositivity.KST.ProExcision.PropA1
public import SerrePositivity.KST.ProExcision.ActionMorphisms
public import SerrePositivity.KST.ProExcision.SetActionMorphisms

/-!
# Proposition A.1 の同変射に関する自然性

概要：係数の同変準同型による二つの bar 比較は可換。
方針：作用圏の対象の射列と transport のラベルを評価する。
規約：KST Proposition A.1、Lemma A.4。作用する G は固定する。
使われ方：係数での m 次比較を半直積のホモロジー比較へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open SerrePositivity.KST.Comparison
variable {G H H' : SimplicialObject MonCat.{u}}
variable {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}

/-- 概要：係数の同変準同型は BH の作用の同変射を誘導する。
方針：BH の各射ラベルに元の同変条件を適用する。
規約：KST Lemma A.4。使われ方：係数作用 bar の写像。 -/
def barSetActionHom (f : SimplicialActionHom A B) :
    SimplicialSetActionHom (barSetAction A) (barSetAction B) where
  base := 𝟙 _
  hom := monoidBarMap f.hom
  equivariant n a p := by
    apply (monoidWordEquiv (H'.obj n) n.unop.len).injective
    funext i
    exact f.equivariant n a _

/-- 概要：係数の同変射が E_BH G に誘導する写像。
方針：BH 上の同変射を作用 bar へ送る。
規約：KST Lemma A.4。使われ方：Proposition A.1 の自然性の左側の射。 -/
def coefficientActionBarMap (f : SimplicialActionHom A B) :
    coefficientActionBar A ⟶ coefficientActionBar B :=
  setActionBarMap (barSetActionHom f)

/-- 概要：作用 bar と半直積 bar の比較は係数の同変射に自然。
方針：各単体の transport の base と fiber を評価する。
規約：KST Proposition A.1、Lemma A.4。
使われ方：係数項と半直積項のホモロジー写像の可換四角形。 -/
theorem actionBarComparison_naturality (f : SimplicialActionHom A B) :
    coefficientActionBarMap f ≫ actionBarComparison B =
      actionBarComparison A ≫ monoidBarMap (simplicialActionProductMap f) := by
  apply NatTrans.ext
  funext n
  letI := A.actionStructure n
  letI := B.actionStructure n
  letI := (barSetAction A).actionStructure n
  letI := (barSetAction B).actionStructure n
  apply ConcreteCategory.hom_ext
  intro p
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ActionProduct.ext <;> rfl

/-- 概要：所有レーンの関手に送った A.1 の同型も同変射に自然。
方針：幾何的な比較の自然性に関手を適用する。
規約：KST Proposition A.1、式 (A.2)。H_* の具体的な定義は所有レーンから借りる。
使われ方：Lemma A.4 の絶対ホモロジー項の比較。 -/
theorem propA1ComparisonIso_naturality {D : Type v} [Category.{w} D]
    (F : SSet.{u} ⥤ D) (hF : SSet.anodyneExtensions.IsInvertedBy F)
    (hG : SimplicialMonoid.IsGrouplike G) (f : SimplicialActionHom A B) :
    F.map (coefficientActionBarMap f) ≫ (propA1ComparisonIso F hF B hG).hom =
      (propA1ComparisonIso F hF A hG).hom ≫
        F.map (monoidBarMap (simplicialActionProductMap f)) := by
  change F.map (coefficientActionBarMap f) ≫ F.map (actionBarComparison B) =
    F.map (actionBarComparison A) ≫ F.map (monoidBarMap (simplicialActionProductMap f))
  rw [← F.map_comp, ← F.map_comp, actionBarComparison_naturality]

end SerrePositivity.KST.ProExcision
