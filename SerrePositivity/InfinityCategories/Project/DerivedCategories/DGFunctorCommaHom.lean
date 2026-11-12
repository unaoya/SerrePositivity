module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaData
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
/-!
概要：実入力・commaの比較正方形を、その比較ホモトピーごと全 Hom 複体へ束ねる。
方針：同じ実差写像の mapping cocone と、全パラメータ複体からの実持ち上げを使う。
規約：Hom 複体と実射影を構成する段階。dg 合成・nerve の普遍性は未証明。
使われ方：β5 の一般commaと、β4 の gluing の実係数模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 実正方形の差と実比較ホモトピーを持つ、候補 dg 圏の全 Hom 複体。 -/
def dgFunctorCommaHomComplex : Complex R :=
  mappingCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y)
/-- 同じ全 Hom 複体の、実入力 Hom への射影。 -/
def dgFunctorCommaSourceHomMap :
    dgFunctorCommaHomComplex R C E F X Y ⟶ homObject R C X.source Y.source :=
  mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) ≫ biprod.fst
/-- 同じ全 Hom 複体の、実比較対象 Hom への射影。 -/
def dgFunctorCommaReplacementHomMap :
    dgFunctorCommaHomComplex R C E F X Y ⟶
      homObject R E X.replacement Y.replacement :=
  mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) ≫ biprod.snd
variable (K : Complex R) (a : K ⟶ homObject R C X.source Y.source)
  (b : K ⟶ homObject R E X.replacement Y.replacement)
  (h : Cochain K (homObject R E X.replacement (F.obj Y.source)) (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom
    (biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) = 0)
/-- 任意の全パラメータ複体から、指定実二射と比較ホモトピーを同時に持ち上げる。 -/
def dgFunctorCommaHomLift : K ⟶ dgFunctorCommaHomComplex R C E F X Y :=
  mappingCocone.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X Y) (biprod.lift a b) h hh
/-- 同じ実持ち上げの入力射影は、指定した同じ実射。 -/
lemma dgFunctorCommaHomLift_source :
    dgFunctorCommaHomLift R C E F X Y K a b h hh ≫
      dgFunctorCommaSourceHomMap R C E F X Y = a := by
  simp only [dgFunctorCommaHomLift, dgFunctorCommaSourceHomMap,
    ← Category.assoc, mappingCocone.lift_fst, biprod.lift_fst]
/-- 同じ実持ち上げの出力射影も、指定した同じ実射。 -/
lemma dgFunctorCommaHomLift_replacement :
    dgFunctorCommaHomLift R C E F X Y K a b h hh ≫
      dgFunctorCommaReplacementHomMap R C E F X Y = b := by
  simp only [dgFunctorCommaHomLift, dgFunctorCommaReplacementHomMap,
    ← Category.assoc, mappingCocone.lift_fst, biprod.lift_snd]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
