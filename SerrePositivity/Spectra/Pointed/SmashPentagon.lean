module

public import SerrePositivity.Spectra.Pointed.SmashAssociator

/-!
# smash 積の pentagon

四変数の各括弧への標準射を比較し、直積の pentagon に帰着する。
標準射のエピ性により、直積上の比較から smash 上の等式が従う。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasFiniteColimits C]

/-- 四変数の左括弧への標準射。 -/
def leftFourQuotient (W X Y Z : PointedObject C) :
    prod (prod (prod W X) Y) Z ⟶ smash (smash (smash W X) Y) Z :=
  prodMap (leftTripleQuotient W X Y) (𝟙 Z) ≫ smashQuotient (smash (smash W X) Y) Z

/-- pentagon の第二の括弧への標準射。 -/
def middleLeftFourQuotient (W X Y Z : PointedObject C) :
    prod (prod W (prod X Y)) Z ⟶ smash (smash W (smash X Y)) Z :=
  prodMap (rightTripleQuotient W X Y) (𝟙 Z) ≫ smashQuotient (smash W (smash X Y)) Z

/-- pentagon の第三の括弧への標準射。 -/
def middleRightFourQuotient (W X Y Z : PointedObject C) :
    prod W (prod (prod X Y) Z) ⟶ smash W (smash (smash X Y) Z) :=
  prodMap (𝟙 W) (leftTripleQuotient X Y Z) ≫ smashQuotient W (smash (smash X Y) Z)

/-- 四変数の右括弧への標準射。 -/
def rightFourQuotient (W X Y Z : PointedObject C) :
    prod W (prod X (prod Y Z)) ⟶ smash W (smash X (smash Y Z)) :=
  prodMap (𝟙 W) (rightTripleQuotient X Y Z) ≫ smashQuotient W (smash X (smash Y Z))

/-- 二組ずつ括った四変数への標準射。 -/
def pairedFourQuotient (W X Y Z : PointedObject C) :
    prod (prod W X) (prod Y Z) ⟶ smash (smash W X) (smash Y Z) :=
  prodMap (smashQuotient W X) (smashQuotient Y Z) ≫
    smashQuotient (smash W X) (smash Y Z)

instance leftFourQuotient_epi (W X Y Z : PointedObject C) : Epi (leftFourQuotient W X Y Z) := by
  dsimp [leftFourQuotient]
  infer_instance

@[reassoc] lemma leftFourQuotient_innerAssoc (W X Y Z : PointedObject C) :
    leftFourQuotient W X Y Z ≫ smashMap (smashAssocHom W X Y) (𝟙 Z) =
      prodMap (prodAssocHom W X Y) (𝟙 Z) ≫ middleLeftFourQuotient W X Y Z := by
  simp only [leftFourQuotient, middleLeftFourQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id,
    leftTripleQuotient_assocHom]

@[reassoc] lemma middleRightFourQuotient_innerAssoc (W X Y Z : PointedObject C) :
    middleRightFourQuotient W X Y Z ≫ smashMap (𝟙 W) (smashAssocHom X Y Z) =
      prodMap (𝟙 W) (prodAssocHom X Y Z) ≫ rightFourQuotient W X Y Z := by
  simp only [middleRightFourQuotient, rightFourQuotient, Category.assoc, smashQuotient_map]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id,
    leftTripleQuotient_assocHom]

@[reassoc] lemma middleLeftFourQuotient_outerAssoc (W X Y Z : PointedObject C) :
    middleLeftFourQuotient W X Y Z ≫ smashAssocHom W (smash X Y) Z =
      prodAssocHom W (prod X Y) Z ≫ middleRightFourQuotient W X Y Z := by
  have h : middleLeftFourQuotient W X Y Z =
      prodMap (prodMap (𝟙 W) (smashQuotient X Y)) (𝟙 Z) ≫
        leftTripleQuotient W (smash X Y) Z := by
    simp [middleLeftFourQuotient, rightTripleQuotient, leftTripleQuotient, ← Category.assoc]
  rw [h, Category.assoc, leftTripleQuotient_assocHom,
    ← Category.assoc, prodAssoc_naturality, Category.assoc]
  simp only [rightTripleQuotient, middleRightFourQuotient, leftTripleQuotient]
  simp only [← Category.assoc, prodMap_comp, Category.id_comp]

@[reassoc] lemma leftFourQuotient_outerAssoc (W X Y Z : PointedObject C) :
    leftFourQuotient W X Y Z ≫ smashAssocHom (smash W X) Y Z =
      prodAssocHom (prod W X) Y Z ≫ pairedFourQuotient W X Y Z := by
  have h : leftFourQuotient W X Y Z =
      prodMap (prodMap (smashQuotient W X) (𝟙 Y)) (𝟙 Z) ≫
        leftTripleQuotient (smash W X) Y Z := by
    simp [leftFourQuotient, leftTripleQuotient, ← Category.assoc]
  rw [h, Category.assoc, leftTripleQuotient_assocHom,
    ← Category.assoc, prodAssoc_naturality, Category.assoc]
  simp only [rightTripleQuotient, pairedFourQuotient]
  simp only [← Category.assoc, prodMap_comp, prodMap_id, Category.id_comp, Category.comp_id]


@[reassoc] lemma pairedFourQuotient_outerAssoc (W X Y Z : PointedObject C) :
    pairedFourQuotient W X Y Z ≫ smashAssocHom W X (smash Y Z) =
      prodAssocHom W X (prod Y Z) ≫ rightFourQuotient W X Y Z := by
  have h : pairedFourQuotient W X Y Z =
      prodMap (prodMap (𝟙 W) (𝟙 X)) (smashQuotient Y Z) ≫
        leftTripleQuotient W X (smash Y Z) := by
    simp [pairedFourQuotient, leftTripleQuotient, ← Category.assoc]
  rw [h, Category.assoc, leftTripleQuotient_assocHom,
    ← Category.assoc, prodAssoc_naturality, Category.assoc]
  simp only [rightTripleQuotient, rightFourQuotient]
  simp only [← Category.assoc, prodMap_comp, Category.comp_id]


/-- smash 積の結合射は pentagon を満たす。 -/
lemma smashAssoc_pentagon (W X Y Z : PointedObject C) :
    smashMap (smashAssocHom W X Y) (𝟙 Z) ≫ smashAssocHom W (smash X Y) Z ≫
      smashMap (𝟙 W) (smashAssocHom X Y Z) =
    smashAssocHom (smash W X) Y Z ≫ smashAssocHom W X (smash Y Z) := by
  apply (cancel_epi (leftFourQuotient W X Y Z)).mp
  rw [leftFourQuotient_innerAssoc_assoc, middleLeftFourQuotient_outerAssoc_assoc,
    middleRightFourQuotient_innerAssoc, leftFourQuotient_outerAssoc_assoc,
    pairedFourQuotient_outerAssoc]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ rightFourQuotient W X Y Z) (prodAssoc_pentagon W X Y Z)

end SerrePositivity.PointedObject
