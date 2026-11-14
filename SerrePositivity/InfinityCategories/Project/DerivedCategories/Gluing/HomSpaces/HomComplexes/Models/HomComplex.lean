module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Objects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeBoundary

/-!
gluing の全 Hom 複体。比較差の mapping cocone を使い、
Hom_C ⊕ Hom_D に加えて φ(d',c)[-1] とその捻れた微分を保持する。
合成・前三角性・nerve 比較はこの定義に仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 比較ホモトピーを含む、双加群に沿う gluing の全 Hom 複体。 -/
abbrev dgGluingHomComplex : Complex R := mappingCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)

/-- 左成分 Hom への実鎖射影。 -/
def dgGluingLeftHomMap : dgGluingHomComplex R C D M X Y ⟶ homObject R C X.left Y.left :=
  mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) ≫ biprod.fst

/-- 右成分 Hom への実鎖射影。 -/
def dgGluingRightHomMap : dgGluingHomComplex R C D M X Y ⟶ homObject R D X.right Y.right :=
  mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) ≫ biprod.snd

/-- 比較ホモトピーを回収する次数 −1 の全 cochain。 -/
def dgGluingHomPrimitive : Cochain (dgGluingHomComplex R C D M X Y)
    (M.value X.left Y.right) (-1) :=
  mappingCocone.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y)

/-- 捻れた微分の比較成分：δh + (gμ − νf) = 0。 -/
lemma dgGluingHomPrimitive_boundary :
    δ (-1) 0 (dgGluingHomPrimitive R C D M X Y) +
      Cochain.ofHom (mappingCocone.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCocone_snd_boundary _

variable (K : Complex R) (a : K ⟶ homObject R C X.left Y.left)
  (b : K ⟶ homObject R D X.right Y.right)
  (h : Cochain K (M.value X.left Y.right) (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom
    (biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDifference R C D M X Y) = 0)

/-- 任意のパラメータ複体の二射と比較ホモトピーを持ち上げる。 -/
def dgGluingHomLift : K ⟶ dgGluingHomComplex R C D M X Y :=
  mappingCocone.lift _ (biprod.lift a b) h hh

@[reassoc] lemma dgGluingHomLift_left :
    dgGluingHomLift R C D M X Y K a b h hh ≫ dgGluingLeftHomMap R C D M X Y = a := by
  simp only [dgGluingHomLift, dgGluingLeftHomMap, ← Category.assoc,
    mappingCocone.lift_fst, biprod.lift_fst]

@[reassoc] lemma dgGluingHomLift_right :
    dgGluingHomLift R C D M X Y K a b h hh ≫ dgGluingRightHomMap R C D M X Y = b := by
  simp only [dgGluingHomLift, dgGluingRightHomMap, ← Category.assoc,
    mappingCocone.lift_fst, biprod.lift_snd]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
