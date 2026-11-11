module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseColimitExistence
public import SerrePositivity.KST.SConstruction.IdentityCocones
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows

/-! # 関手圏の余極限の添字の制限
概要：点ごとの余極限が存在する図式の余極限は、パラメーターの前合成で保たれる。
方針：余極限を各点で評価してから、前合成と評価の可換性を使う。
規約：HTT 5.1.2.2 の存在前提を保持する。使われ方：Ar[n] の部分図式への cofiber の普遍性の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：関手圏の余錐を添字の前合成で制限する。
方針：内部 Hom の前合成で余錐と図式を同時に後合成する。
規約：余極限性を仮定せず定義する。使われ方：部分図式の普遍性の比較。 -/
def reindexFunctorCocone {J K L X : SSet.{u}} {p : J ⟶ (ihom K).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (f : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ (pre f).app X) :=
  ⟨c.val ≫ (pre f).app X, by rw [← Category.assoc, c.property]⟩

/-- 概要：点ごとに普遍な余錐は添字の前合成後も点ごとに普遍。
方針：前合成した余錐の評価を、元の余錐の像の頂点での評価と同定する。
規約：X の quasicategory 性を要求しない。使われ方：cofiber 族の有限部分への制限。 -/
lemma IsPointwiseColimitCone.reindex {J K L X : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone c)
    (f : L ⟶ K) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone (reindexFunctorCocone c f) := by
  intro l
  apply (isColimitCone_iff_of_map_eq _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorCocone c (f.app (Opposite.op ⦋0⦌) l)) ?_).2
      (hc (f.app (Opposite.op ⦋0⦌) l))
  change (c.val ≫ (pre f).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l =
    c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (f.app (Opposite.op ⦋0⦌) l)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsPointwiseColimitCone export _root_.SerrePositivity.KST.SConstruction.IsPointwiseColimitCone (reindex)

/-- 概要：各点で余極限が存在すれば、関手圏の余極限余錐は任意の添字の前合成で保たれる。
方針：関手圏の余極限を点ごとの余極限に戻し、評価を制限して再び関手圏に移す。
規約：X は quasicategory、f は任意。使われ方：構成した普遍四角形の添字の制限。 -/
lemma isColimitCone_reindex_of_hasPointwiseColimits {J K L X : SSet.{u}}
    [Quasicategory X] {p : J ⟶ (ihom K).obj X} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasPointwiseColimits p)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (f : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (reindexFunctorCocone c f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_pointwise
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits hp c hc).reindex f

end SerrePositivity.KST.SConstruction
