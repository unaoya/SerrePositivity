module
public import SerrePositivity.KST.SConstruction.ClosedPredicateOperations

/-! # 相対 cofiber 図式 E(A,C,B)
概要：subobject が A、quotient が B に入る全 cofiber 図式を安定な入力として構成する。
方針：二つの完全な評価による閉じた条件の逆像を交差させる。
規約：全 cofiber の選択を保ち、加法性は別に証明する。使われ方：Fiore–Pieper の相対加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 相対 cofiber 図式の subobject・quotient による安定な閉性条件。 -/
def relativeCofiberPredicate {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    ClosedStablePredicate (cofiberStableModel X) :=
  (A.comap (cofiberStableSubobject X)).inter (B.comap (cofiberStableQuotient X))

/-- 相対 cofiber 図式 E(A,C,B) の全高次単体を持つ単体集合。 -/
def relativeCofiberDiagrams {X : StableModel.{u}} (A B : ClosedStablePredicate X) : SSet.{u} :=
  closedSubcategory (relativeCofiberPredicate A B)

/-- 相対 cofiber 図式は quasicategory。 -/
instance relativeCofiberDiagrams_quasicategory {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) : Quasicategory (relativeCofiberDiagrams A B) :=
  inferInstanceAs (Quasicategory (closedSubcategory (relativeCofiberPredicate A B)))

/-- 相対 cofiber 図式は零対象・普遍四角形の閉性から実際に安定。 -/
instance relativeCofiberDiagrams_isStable {X : StableModel.{u}}
    (A B : ClosedStablePredicate X) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (relativeCofiberDiagrams A B) :=
  inferInstanceAs (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (closedSubcategory (relativeCofiberPredicate A B)))

/-- 相対 E(A,C,B) を安定な入力の模型として束ねる。 -/
def relativeCofiberStableModel {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    StableModel.{u} := closedStableModel (relativeCofiberPredicate A B)

/-- 相対 cofiber 図式の全 cofiber 図式への包含は完全。 -/
def relativeCofiberInclusion {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberStableModel A B ⟶ cofiberStableModel X :=
  closedStableInclusion (relativeCofiberPredicate A B)

/-- 相対 cofiber 図式の頂点は二つの元の部分圏条件を満たす。 -/
lemma relativeCofiber_vertex {X : StableModel.{u}} (A B : ClosedStablePredicate X)
    (v : (relativeCofiberDiagrams A B) _⦋0⦌) :
    A.predicate ((cofiberStableSubobject X).val.app (Opposite.op ⦋0⦌) v.val) ∧
      B.predicate ((cofiberStableQuotient X).val.app (Opposite.op ⦋0⦌) v.val) :=
  closedSubcategory_vertex (relativeCofiberPredicate A B) v

/-- 相対 cofiber 図式から A への元の subobject の射。 -/
def relativeCofiberSubobjectMap {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberDiagrams A B ⟶ closedSubcategory A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift A.predicate
    ((relativeCofiberInclusion A B).val ≫ (cofiberStableSubobject X).val)
    (fun v => (relativeCofiber_vertex A B v).1)

/-- 相対 cofiber 図式から B への元の quotient の射。 -/
def relativeCofiberQuotientMap {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberDiagrams A B ⟶ closedSubcategory B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift B.predicate
    ((relativeCofiberInclusion A B).val ≫ (cofiberStableQuotient X).val)
    (fun v => (relativeCofiber_vertex A B v).2)

/-- 相対 subobject の射は A の包含を通すと元の評価を回収する。 -/
lemma relativeCofiberSubobjectMap_ι {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberSubobjectMap A B ≫ (closedStableInclusion A).val =
      (relativeCofiberInclusion A B).val ≫ (cofiberStableSubobject X).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 相対 quotient の射は B の包含を通すと元の評価を回収する。 -/
lemma relativeCofiberQuotientMap_ι {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberQuotientMap A B ≫ (closedStableInclusion B).val =
      (relativeCofiberInclusion A B).val ≫ (cofiberStableQuotient X).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 相対 subobject の射は完全。 -/
def relativeCofiberSubobject {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberStableModel A B ⟶ closedStableModel A :=
  ⟨relativeCofiberSubobjectMap A B, by
    apply preservesCofiberData_fullSubcomplex_of_comp A.predicate
    change PreservesCofiberData (relativeCofiberSubobjectMap A B ≫ (closedStableInclusion A).val)
    rw [relativeCofiberSubobjectMap_ι]
    exact (relativeCofiberInclusion A B).property.comp (cofiberStableSubobject X).property⟩

/-- 相対 quotient の射は完全。 -/
def relativeCofiberQuotient {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberStableModel A B ⟶ closedStableModel B :=
  ⟨relativeCofiberQuotientMap A B, by
    apply preservesCofiberData_fullSubcomplex_of_comp B.predicate
    change PreservesCofiberData (relativeCofiberQuotientMap A B ≫ (closedStableInclusion B).val)
    rw [relativeCofiberQuotientMap_ι]
    exact (relativeCofiberInclusion A B).property.comp (cofiberStableQuotient X).property⟩

/-- 相対 subobject の完全関手は包含によって元の評価と厳密に可換。 -/
lemma relativeCofiberSubobject_inclusion {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberSubobject A B ≫ closedStableInclusion A =
      relativeCofiberInclusion A B ≫ cofiberStableSubobject X :=
  Subtype.ext (relativeCofiberSubobjectMap_ι A B)

/-- 相対 quotient の完全関手も包含によって元の評価と厳密に可換。 -/
lemma relativeCofiberQuotient_inclusion {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    relativeCofiberQuotient A B ≫ closedStableInclusion B =
      relativeCofiberInclusion A B ≫ cofiberStableQuotient X :=
  Subtype.ext (relativeCofiberQuotientMap_ι A B)

end SerrePositivity.KST.SConstruction
