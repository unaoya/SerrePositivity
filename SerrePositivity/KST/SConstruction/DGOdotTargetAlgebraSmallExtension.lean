module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallExtension
public import SerrePositivity.KST.SConstruction.DGOdotTargetAlgebraRepresentation
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionClosedNaturality

/-! # 元の ⊙ 比較代数射と同じ小模型での一回 Perf 延長
概要：元の cone 作用の一回延長を、元の比較代数射の延長と同じ小模型で照合する。
方針：元の End への厳密因子分解と全 Hom 比較を前合成し、同じ標準合成比較へつなぐ。
規約：元の代数射・同じ cone 点・全次数を保持。使われ方：具体的 LT の実 Perf 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "H" => dgOdotAlgebraToEnd R d
local notation "c" => (Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.corner d))

/-- 元の ⊙ から指定商 End を経由する、同じ小模型内の実 cone 作用。 -/
def dgOdotConeAlgebraSmallFunctor : DGFunctor R (B) (DGOdotTargetSmallPerfect R d) :=
  (H).comp (dgOdotConeSmallRepresentation R d)

/-- 元の比較代数射を、そのまま同じ小模型の元の Yoneda へ送る実関手。 -/
def dgOdotTargetAlgebraSmallFunctor : DGFunctor R (B) (DGOdotTargetSmallPerfect R d) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)).comp (dgOdotTargetSmallYoneda R d)

/-- 元の比較代数射の実小模型での作用は、同じ元の商 End 比較を厳密に回収する。 -/
lemma dgOdotTargetAlgebraSmallFunctor_factor :
    (H).comp (dgOdotTargetSmallRepresentation R d) = dgOdotTargetAlgebraSmallFunctor R d := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (H).comp (dgOdotTargetSmallRepresentation R d))
    (G := dgOdotTargetAlgebraSmallFunctor R d) (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ (((dgOdotTargetCornerEndMap R d).map
    EndomorphismObject.point EndomorphismObject.point ≫ 𝟙 _) ≫
      (dgOdotTargetSmallYoneda R d).map (c) (c))) ≫ eqToHom (by rfl) =
    (dgOdotTargetMap R d).hom ≫ (dgOdotTargetSmallYoneda R d).map (c) (c)
  rw [eqToHom_refl, Category.comp_id, Category.id_comp, Category.comp_id, dgOdotTargetMap_hom]
  rfl

/-- 元の厳密因子分解を、対象を固定した同じ全 Hom の等号として回収する。 -/
lemma dgOdotTargetAlgebraSmallFunctor_map (x y : B) :
    (dgOdotTargetAlgebraSmallFunctor R d).map x y =
      (H).map x y ≫ (dgOdotTargetSmallRepresentation R d).map ((H).obj x) ((H).obj y) := by
  change (dgOdotTargetMap R d).hom ≫ (dgOdotTargetSmallYoneda R d).map (c) (c) =
    𝟙 _ ≫ (((dgOdotTargetCornerEndMap R d).map EndomorphismObject.point
      EndomorphismObject.point ≫ 𝟙 _) ≫ (dgOdotTargetSmallYoneda R d).map (c) (c))
  rw [Category.id_comp, Category.comp_id, dgOdotTargetMap_hom]
  rfl

/-- 元の cone 同型は、元の ⊙ からの二つの小模型内の作用に全 Hom 自然。 -/
lemma dgOdotAlgebraSmallPointIso_naturality (x y : B) :
    (dgOdotConeAlgebraSmallFunctor R d).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallConePoint R d))
      (dgOdotTargetSmallPointIso R d).hom =
    (dgOdotTargetAlgebraSmallFunctor R d).map x y ≫ eHomWhiskerRight (Complex R)
      (dgOdotTargetSmallPointIso R d).hom
      (ForgetEnrichment.of (Complex R) (dgOdotTargetSmallRepresentablePoint R d)) := by
  rw [dgOdotTargetAlgebraSmallFunctor_map]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (H).map x y ≫ f)
      (dgOdotTargetSmallPointIso_naturality R d ((H).obj x) ((H).obj y))).trans
        (Category.assoc _ _ _).symm)

/-- 元の ⊙ の各実 perfect 入力上での、同じ小模型への二つの一回延長の同型。 -/
def dgOdotAlgebraSmallPerfectAt (M : PerfectDGModule R (B)) :
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
        (dgOdotConeAlgebraSmallFunctor R d)).obj M) ≅
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
        (dgOdotTargetAlgebraSmallFunctor R d)).obj M) :=
  perfectDGExtensionClosedIsoFromFamilyAt R (B) (DGOdotTargetSmallPerfect R d)
    (dgOdotConeAlgebraSmallFunctor R d) (dgOdotTargetAlgebraSmallFunctor R d)
    (fun _ => dgOdotTargetSmallPointIso R d) (dgOdotAlgebraSmallPointIso_naturality R d) M

/-- 同じ二つの一回延長の同型は、全実 perfect 入力の全 Hom に自然。 -/
lemma dgOdotAlgebraSmallPerfectAt_naturality (X Y : PerfectDGModule R (B)) :
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
      (dgOdotConeAlgebraSmallFunctor R d)).map X Y ≫ eHomWhiskerLeft (Complex R) _
        (dgOdotAlgebraSmallPerfectAt R d Y).hom =
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetAlgebraSmallFunctor R d)).map X Y ≫ eHomWhiskerRight (Complex R)
        (dgOdotAlgebraSmallPerfectAt R d X).hom _ :=
  perfectDGExtensionClosedIsoFromFamilyAt_naturality R (B) (DGOdotTargetSmallPerfect R d)
    (dgOdotConeAlgebraSmallFunctor R d) (dgOdotTargetAlgebraSmallFunctor R d)
    (fun _ => dgOdotTargetSmallPointIso R d) (dgOdotAlgebraSmallPointIso_naturality R d) X Y

/-- 元の比較代数射の実延長と、同じ cone 作用の一回延長との指定同型。 -/
def dgOdotTargetAlgebraSmallPerfectAt (M : PerfectDGModule R (B)) :
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
        (dgOdotConeAlgebraSmallFunctor R d)).obj M) ≅
    ForgetEnrichment.of (Complex R)
      (((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
        (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d)
          (dgOdotTargetSmallYoneda R d))).obj M) :=
  dgOdotAlgebraSmallPerfectAt R d M ≪≫
    (perfectDGExtensionCompositionAt R (B) (E) (DGOdotTargetSmallPerfect R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d) M).symm

/-- 同じ元の合成比較を通す延長同型も、全 Hom に関して自然。 -/
lemma dgOdotTargetAlgebraSmallPerfectAt_naturality (X Y : PerfectDGModule R (B)) :
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
      (dgOdotConeAlgebraSmallFunctor R d)).map X Y ≫ eHomWhiskerLeft (Complex R) _
        (dgOdotTargetAlgebraSmallPerfectAt R d Y).hom =
    ((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
      (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d)
        (dgOdotTargetSmallYoneda R d))).map X Y ≫ eHomWhiskerRight (Complex R)
          (dgOdotTargetAlgebraSmallPerfectAt R d X).hom _ := by
  have hi := dgFunctorClosedComparison_inv_naturality R
    ((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
      (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d) (dgOdotTargetSmallYoneda R d)))
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetAlgebraSmallFunctor R d))
    (fun M => perfectDGExtensionCompositionAt R (B) (E) (DGOdotTargetSmallPerfect R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d) M)
    (perfectDGExtensionCompositionAt_naturality R (B) (E) (DGOdotTargetSmallPerfect R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d)) X Y
  exact dgClosedComparison_comp (Complex R)
    (dgOdotAlgebraSmallPerfectAt R d X).hom (dgOdotAlgebraSmallPerfectAt R d Y).hom
    (perfectDGExtensionCompositionAt R (B) (E) (DGOdotTargetSmallPerfect R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d) X).inv
    (perfectDGExtensionCompositionAt R (B) (E) (DGOdotTargetSmallPerfect R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d) Y).inv _ _ _
    (dgOdotAlgebraSmallPerfectAt_naturality R d X Y) hi

/-- 元の cone と元の比較代数射の実延長を結ぶ、全次数自然な指定比較。 -/
def dgOdotTargetAlgebraSmallPerfectComparison :=
  dgFunctorClosedComparison R
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d) (dgOdotConeAlgebraSmallFunctor R d))
    ((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
      (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d) (dgOdotTargetSmallYoneda R d)))
    (fun M => (dgOdotTargetAlgebraSmallPerfectAt R d M).hom)
    (dgOdotTargetAlgebraSmallPerfectAt_naturality R d)

/-- 同じ指定同型の逆を保つ、実延長の全次数逆比較。 -/
def dgOdotTargetAlgebraSmallPerfectInverseComparison :=
  dgFunctorClosedInverseComparison R
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d) (dgOdotConeAlgebraSmallFunctor R d))
    ((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
      (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d) (dgOdotTargetSmallYoneda R d)))
    (dgOdotTargetAlgebraSmallPerfectAt R d) (dgOdotTargetAlgebraSmallPerfectAt_naturality R d)

/-- 同じ元の実延長と指定同型を保つ、閉零射圏の自然同型。 -/
def dgOdotTargetAlgebraSmallPerfectClosedIso :
    (perfectDGExtension R (B) (DGOdotTargetSmallPerfect R d)
      (dgOdotConeAlgebraSmallFunctor R d)).onClosed ≅
    ((perfectDGExtension R (B) (E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).comp
      (perfectDGExtension R (E) (DGOdotTargetSmallPerfect R d)
        (dgOdotTargetSmallYoneda R d))).onClosed :=
  dgFunctorClosedComparisonIso R _ _ (dgOdotTargetAlgebraSmallPerfectAt R d)
    (dgOdotTargetAlgebraSmallPerfectAt_naturality R d)

end SerrePositivity.KST.SConstruction
