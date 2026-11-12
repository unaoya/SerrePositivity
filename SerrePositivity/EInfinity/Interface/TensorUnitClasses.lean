module

public import SerrePositivity.EInfinity.Interface.TensorLegs
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
# 離散基底代数からの単位の類

概要：HA 3.2.4.7 の標準テンソル射で使う単位の H⁰ の類を定める。
方針：離散基底環の指定比較と通常の解像度の増大を通して、単位射の像を読む。
規約：CAlg の模型も、その特定の π₀ の環の模型も参照しない。
使われ方：単位の閉次数零の代表の正規化と coproduct_tensor_legs。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard
variable (S : Type u) [CommRing S]

/-- 基底環自身を、基底環の下の可換環として読む。 -/
def baseRingAlgebra : RingAlgebra S := Under.mk (𝟙 (CommRingCat.of S))

/-- 基底代数の台の加群は、基底環の正則加群。 -/
def baseRingAlgebraModuleIso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule S).obj (baseRingAlgebra S) ≅ ModuleCat.of S S :=
  LinearEquiv.toModuleIso
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- 抽象 CAlg の離散基底環の指定頂点。 -/
def coreUnitVertex (E : EInfinityCore.{u}) : (E.CAlg S) _⦋0⦌ :=
  atVertex (E.discrete S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (baseRingAlgebra S))

/-- 通常のホモトピー圏上の零次ホモロジー。 -/
abbrev vertexHZeroFunctor :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)).inverse ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor S 0

/-- 離散基底環からの指定比較は、その台の H⁰ を基底環と同定する。 -/
def coreUnitHZeroIso (E : EInfinityCore.{u}) :
    (vertexHZeroFunctor S).obj
      (SSet.HomotopyCategory.mk (atVertex (E.forget S) (coreUnitVertex S E))) ≅
        ModuleCat.of S S :=
  (vertexHZeroFunctor S).mapIso
    ((E.discrete_forget S).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (baseRingAlgebra S))) ≪≫
  vertexHZeroRepresentativeIso S
    (atVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbedding S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (baseRingAlgebra S))) ≪≫
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteEmbeddingHomologyZeroIso S (baseRingAlgebra S) ≪≫ baseRingAlgebraModuleIso S

/-- 単位代数からの射が定める、同じ具体的な代表の H⁰ の単位の類。 -/
def coreUnitClass (E : EInfinityCore.{u}) (x : (E.CAlg S) _⦋0⦌)
    (h : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk x) :
    ModuleCat.of S S ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) x)).val.homology 0 :=
  (coreUnitHZeroIso S E).inv ≫
    (vertexHZeroFunctor S).map ((hoFunctor.map (E.forget S)).toFunctor.map h) ≫
      (vertexHZeroRepresentativeIso S (atVertex (E.forget S) x)).hom

/-- 複体の単位からの鎖写像が、指定した単位射の同じ H⁰ の類を表す条件。 -/
def NormalizedTensorUnit (E : EInfinityCore.{u}) (x : (E.CAlg S) _⦋0⦌)
    (h : (SSet.HomotopyCategory.mk (coreUnitVertex S E) : (E.CAlg S).HomotopyCategory) ⟶
      SSet.HomotopyCategory.mk x)
    (unitX : 𝟙_ (Complex S) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategoryVertexEquiv S (atVertex (E.forget S) x)).val) : Prop :=
  (complexUnitHZeroIso S).inv ≫ HomologicalComplex.homologyMap unitX 0 = coreUnitClass S E x h

end SerrePositivity.EInfinity
