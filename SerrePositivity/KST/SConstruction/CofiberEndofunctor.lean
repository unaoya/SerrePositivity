module
public import SerrePositivity.KST.SConstruction.CofiberPostcomposition

/-! # 全 cofiber 図式の安定な入力上の自己関手
概要：全 cofiber 図式を完全関手に関して関手化し、各角の評価を自然変換にする。
方針：内部 Hom の後合成の完全性を全部分複体へ反映する。
規約：零角を固定せず、恒等・合成は厳密。使われ方：反復加法性の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全部分複体への射の完全性は周囲への合成の完全性から反映される。 -/
lemma preservesCofiberData_fullSubcomplex_of_comp {X Y : SSet.{u}} [Quasicategory Y]
    (P : Y _⦋0⦌ → Prop) (f : X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P : SSet.{u}))
    (hf : PreservesCofiberData (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P).ι)) :
    PreservesCofiberData f := by
  constructor
  · intro z hz
    have hv := hf.1 z hz
    exact ⟨isInitialVertex_fullSubcomplex_of_ambient P _ hv.1,
      isTerminalVertex_fullSubcomplex_of_ambient P _ hv.2⟩
  · intro t ht
    apply isPushoutSquare_fullSubcomplex_of_ambient P
    simpa only [Category.assoc] using hf.2 t ht

/-- 全 cofiber 図式の後合成は完全。 -/
lemma cofiberPostcomp_preservesCofiberData {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesCofiberData f) :
    PreservesCofiberData (cofiberPostcomp f hf) := by
  apply preservesCofiberData_fullSubcomplex_of_comp IsCofiberDiagramVertex
  rw [cofiberPostcomp_ι]
  exact (cofiberInclusion_preservesSConstructionData C).toCofiberData.comp
    (ihom_map_preservesCofiberData f hf)

/-- cofiber 図式の後合成は恒等射を保つ。 -/
lemma cofiberPostcomp_id (C : SSet.{u}) :
    cofiberPostcomp (𝟙 C) (preservesCofiberData_id C) = 𝟙 (cofiberDiagrams C) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).1
  erw [cofiberPostcomp_ι, CategoryTheory.Functor.map_id]

/-- cofiber 図式の後合成は完全関手の合成を保つ。 -/
lemma cofiberPostcomp_comp {C D E : SSet.{u}} (f : C ⟶ D) (g : D ⟶ E)
    (hf : PreservesCofiberData f) (hg : PreservesCofiberData g) :
    cofiberPostcomp (f ≫ g) (hf.comp hg) = cofiberPostcomp f hf ≫ cofiberPostcomp g hg := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι).1
  rw [cofiberPostcomp_ι, Category.assoc, cofiberPostcomp_ι, ← Category.assoc,
    cofiberPostcomp_ι, Functor.map_comp, Category.assoc]

/-- 全 cofiber 図式の安定な入力の圏上の自己関手。 -/
def cofiberEndofunctor : StableModel.{u} ⥤ StableModel.{u} where
  obj X := cofiberStableModel X
  map f := ⟨cofiberPostcomp f.val f.property, cofiberPostcomp_preservesCofiberData f.val f.property⟩
  map_id X := Subtype.ext (cofiberPostcomp_id X.carrier)
  map_comp f g := Subtype.ext (cofiberPostcomp_comp f.val g.val f.property g.property)

/-- 全ての角の評価は安定な入力に関して自然な完全関手。 -/
def cofiberEvaluationNat (q : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌) :
    cofiberEndofunctor.{u} ⟶ 𝟭 StableModel.{u} where
  app X := cofiberStableEvaluation X q
  naturality {_X _Y} f := Subtype.ext (cofiberPostcomp_evaluation f.val f.property q)

/-- subobject は cofiber 自己関手から恒等関手への自然変換。 -/
def cofiberSubobjectNat : cofiberEndofunctor.{u} ⟶ 𝟭 StableModel.{u} :=
  cofiberEvaluationNat (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)

/-- quotient は cofiber 自己関手から恒等関手への自然変換。 -/
def cofiberQuotientNat : cofiberEndofunctor.{u} ⟶ 𝟭 StableModel.{u} :=
  cofiberEvaluationNat (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)

end SerrePositivity.KST.SConstruction
